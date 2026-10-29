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
uint8_t l_Lean_Name_isInternal(lean_object*);
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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* lean_thunk_get_own(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_Lean_versionString;
lean_object* l_Lean_ConstMap_toList(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object* v_n_576_, lean_object* v_v_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_a_583_; lean_object* v_snd_584_; 
if (lean_obj_tag(v_v_577_) == 7)
{
lean_object* v_val_590_; lean_object* v_all_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; 
v_val_590_ = lean_ctor_get(v_v_577_, 0);
lean_inc_ref(v_val_590_);
lean_dec_ref_known(v_v_577_, 1);
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
lean_dec_ref(v_v_577_);
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
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object* v_n_596_, lean_object* v_v_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_LeanExport_initState___lam__0(v_n_596_, v_v_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_n_596_);
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
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(lean_object* v_t_625_, lean_object* v_f_626_, lean_object* v_init_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
switch(lean_obj_tag(v_t_625_))
{
case 0:
{
lean_object* v_key_632_; lean_object* v_val_633_; lean_object* v___x_634_; 
v_key_632_ = lean_ctor_get(v_t_625_, 0);
lean_inc(v_key_632_);
v_val_633_ = lean_ctor_get(v_t_625_, 1);
lean_inc(v_val_633_);
lean_dec_ref_known(v_t_625_, 2);
lean_inc_ref(v___y_629_);
v___x_634_ = lean_apply_7(v_f_626_, v_init_627_, v_key_632_, v_val_633_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
return v___x_634_;
}
case 1:
{
lean_object* v_children_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_651_; 
v_children_635_ = lean_ctor_get(v_t_625_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_t_625_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_t_625_, 0);
lean_dec(v_unused_652_);
v___x_637_ = v_t_625_;
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_children_635_);
lean_dec(v_t_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v_children_635_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_children_635_);
lean_dec_ref(v_f_626_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
lean_ctor_set(v___x_637_, 1, v___y_628_);
lean_ctor_set(v___x_637_, 0, v_init_627_);
v___x_643_ = v___x_637_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_init_627_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___y_628_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___y_630_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_637_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_640_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(v_f_626_, v_children_635_, v___x_648_, v___x_649_, v_init_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec_ref(v_children_635_);
return v___x_650_;
}
}
}
default: 
{
lean_object* v_key_653_; lean_object* v_val_654_; lean_object* v_children_655_; lean_object* v___x_656_; 
v_key_653_ = lean_ctor_get(v_t_625_, 0);
lean_inc(v_key_653_);
v_val_654_ = lean_ctor_get(v_t_625_, 1);
lean_inc(v_val_654_);
v_children_655_ = lean_ctor_get(v_t_625_, 2);
lean_inc_ref(v_children_655_);
lean_dec_ref_known(v_t_625_, 3);
lean_inc_ref(v_f_626_);
lean_inc_ref(v___y_629_);
v___x_656_ = lean_apply_7(v_f_626_, v_init_627_, v_key_653_, v_val_654_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v_fst_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
v_fst_658_ = lean_ctor_get(v_a_657_, 0);
if (lean_obj_tag(v_fst_658_) == 0)
{
lean_dec(v_a_657_);
lean_dec_ref(v_children_655_);
lean_dec_ref(v_f_626_);
return v___x_656_;
}
else
{
lean_object* v_a_659_; lean_object* v_snd_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_a_659_ = lean_ctor_get(v_fst_658_, 0);
lean_inc(v_a_659_);
v_snd_660_ = lean_ctor_get(v_a_657_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_657_);
v_fst_661_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_661_);
v_snd_662_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_662_);
lean_dec(v_a_659_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v_children_655_);
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_snd_662_);
lean_dec(v_fst_661_);
lean_dec(v_snd_660_);
lean_dec_ref(v_children_655_);
lean_dec_ref(v_f_626_);
return v___x_656_;
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_656_, 1);
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_664_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(v_f_626_, v_children_655_, v___x_666_, v___x_667_, v_fst_661_, v_snd_662_, v___y_629_, v_snd_660_);
lean_dec_ref(v_children_655_);
return v___x_668_;
}
}
}
else
{
lean_dec_ref(v_children_655_);
lean_dec_ref(v_f_626_);
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(lean_object* v_f_669_, lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_array_uget_borrowed(v_as_670_, v_i_671_);
lean_inc_ref(v_f_669_);
lean_inc(v___x_679_);
v___x_680_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(v___x_679_, v_f_669_, v_b_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v_fst_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_fst_682_ = lean_ctor_get(v_a_681_, 0);
if (lean_obj_tag(v_fst_682_) == 0)
{
lean_dec_ref(v_f_669_);
return v___x_680_;
}
else
{
lean_object* v_a_683_; lean_object* v_snd_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; size_t v___x_687_; size_t v___x_688_; 
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v_a_683_ = lean_ctor_get(v_fst_682_, 0);
lean_inc(v_a_683_);
v_snd_684_ = lean_ctor_get(v_a_681_, 1);
lean_inc(v_snd_684_);
lean_dec(v_a_681_);
v_fst_685_ = lean_ctor_get(v_a_683_, 0);
lean_inc(v_fst_685_);
v_snd_686_ = lean_ctor_get(v_a_683_, 1);
lean_inc(v_snd_686_);
lean_dec(v_a_683_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_671_, v___x_687_);
v_i_671_ = v___x_688_;
v_b_673_ = v_fst_685_;
v___y_674_ = v_snd_686_;
v___y_676_ = v_snd_684_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_669_);
return v___x_680_;
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_f_669_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_b_673_);
lean_ctor_set(v___x_690_, 1, v___y_674_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_676_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_f_694_, lean_object* v_as_695_, lean_object* v_i_696_, lean_object* v_stop_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
size_t v_i_boxed_703_; size_t v_stop_boxed_704_; lean_object* v_res_705_; 
v_i_boxed_703_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_stop_boxed_704_ = lean_unbox_usize(v_stop_697_);
lean_dec(v_stop_697_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(v_f_694_, v_as_695_, v_i_boxed_703_, v_stop_boxed_704_, v_b_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_as_695_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_t_706_, lean_object* v_f_707_, lean_object* v_init_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(v_t_706_, v_f_707_, v_init_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_t_714_, lean_object* v_f_715_, lean_object* v_init_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
switch(lean_obj_tag(v_t_714_))
{
case 0:
{
lean_object* v_tree_721_; lean_object* v___x_722_; 
v_tree_721_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_tree_721_);
lean_dec_ref_known(v_t_714_, 2);
v___x_722_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(v_tree_721_, v_f_715_, v_init_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_722_;
}
case 1:
{
lean_object* v_key_723_; lean_object* v_entry_x3f_724_; lean_object* v_children_725_; lean_object* v_s_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; 
v_key_723_ = lean_ctor_get(v_t_714_, 0);
lean_inc(v_key_723_);
v_entry_x3f_724_ = lean_ctor_get(v_t_714_, 1);
lean_inc(v_entry_x3f_724_);
v_children_725_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_children_725_);
lean_dec_ref_known(v_t_714_, 3);
if (lean_obj_tag(v_entry_x3f_724_) == 1)
{
lean_object* v_val_741_; lean_object* v_fst_742_; lean_object* v___x_743_; 
v_val_741_ = lean_ctor_get(v_entry_x3f_724_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_entry_x3f_724_, 1);
v_fst_742_ = lean_ctor_get(v_val_741_, 0);
lean_inc(v_fst_742_);
lean_dec(v_val_741_);
lean_inc_ref(v_f_715_);
lean_inc_ref(v___y_718_);
v___x_743_ = lean_apply_7(v_f_715_, v_init_716_, v_key_723_, v_fst_742_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_fst_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
v_fst_745_ = lean_ctor_get(v_a_744_, 0);
if (lean_obj_tag(v_fst_745_) == 0)
{
lean_dec(v_a_744_);
lean_dec_ref(v_children_725_);
lean_dec_ref(v_f_715_);
return v___x_743_;
}
else
{
lean_object* v_a_746_; lean_object* v_snd_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; 
lean_dec_ref_known(v___x_743_, 1);
v_a_746_ = lean_ctor_get(v_fst_745_, 0);
lean_inc(v_a_746_);
v_snd_747_ = lean_ctor_get(v_a_744_, 1);
lean_inc(v_snd_747_);
lean_dec(v_a_744_);
v_fst_748_ = lean_ctor_get(v_a_746_, 0);
lean_inc(v_fst_748_);
v_snd_749_ = lean_ctor_get(v_a_746_, 1);
lean_inc(v_snd_749_);
lean_dec(v_a_746_);
v_s_727_ = v_fst_748_;
v___y_728_ = v_snd_749_;
v___y_729_ = v___y_718_;
v___y_730_ = v_snd_747_;
goto v___jp_726_;
}
}
else
{
lean_dec_ref(v_children_725_);
lean_dec_ref(v_f_715_);
return v___x_743_;
}
}
else
{
lean_dec(v_entry_x3f_724_);
lean_dec(v_key_723_);
v_s_727_ = v_init_716_;
v___y_728_ = v___y_717_;
v___y_729_ = v___y_718_;
v___y_730_ = v___y_719_;
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_array_get_size(v_children_725_);
v___x_733_ = lean_nat_dec_lt(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_children_725_);
lean_dec_ref(v_f_715_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_s_727_);
lean_ctor_set(v___x_734_, 1, v___y_728_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___y_730_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_732_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(v_f_715_, v_children_725_, v___x_738_, v___x_739_, v_s_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec_ref(v_children_725_);
return v___x_740_;
}
}
}
default: 
{
lean_object* v_key_750_; lean_object* v_entry_x3f_751_; lean_object* v_children_752_; lean_object* v_s_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; 
v_key_750_ = lean_ctor_get(v_t_714_, 0);
lean_inc(v_key_750_);
v_entry_x3f_751_ = lean_ctor_get(v_t_714_, 1);
lean_inc(v_entry_x3f_751_);
v_children_752_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_children_752_);
lean_dec_ref_known(v_t_714_, 3);
if (lean_obj_tag(v_entry_x3f_751_) == 1)
{
lean_object* v_val_769_; lean_object* v_fst_770_; lean_object* v___x_771_; 
v_val_769_ = lean_ctor_get(v_entry_x3f_751_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_entry_x3f_751_, 1);
v_fst_770_ = lean_ctor_get(v_val_769_, 0);
lean_inc(v_fst_770_);
lean_dec(v_val_769_);
lean_inc_ref(v_f_715_);
lean_inc_ref(v___y_718_);
v___x_771_ = lean_apply_7(v_f_715_, v_init_716_, v_key_750_, v_fst_770_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v_fst_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
v_fst_773_ = lean_ctor_get(v_a_772_, 0);
if (lean_obj_tag(v_fst_773_) == 0)
{
lean_dec(v_a_772_);
lean_dec_ref(v_children_752_);
lean_dec_ref(v_f_715_);
return v___x_771_;
}
else
{
lean_object* v_a_774_; lean_object* v_snd_775_; lean_object* v_fst_776_; lean_object* v_snd_777_; 
lean_dec_ref_known(v___x_771_, 1);
v_a_774_ = lean_ctor_get(v_fst_773_, 0);
lean_inc(v_a_774_);
v_snd_775_ = lean_ctor_get(v_a_772_, 1);
lean_inc(v_snd_775_);
lean_dec(v_a_772_);
v_fst_776_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_fst_776_);
v_snd_777_ = lean_ctor_get(v_a_774_, 1);
lean_inc(v_snd_777_);
lean_dec(v_a_774_);
v_s_754_ = v_fst_776_;
v___y_755_ = v_snd_777_;
v___y_756_ = v___y_718_;
v___y_757_ = v_snd_775_;
goto v___jp_753_;
}
}
else
{
lean_dec_ref(v_children_752_);
lean_dec_ref(v_f_715_);
return v___x_771_;
}
}
else
{
lean_dec(v_entry_x3f_751_);
lean_dec(v_key_750_);
v_s_754_ = v_init_716_;
v___y_755_ = v___y_717_;
v___y_756_ = v___y_718_;
v___y_757_ = v___y_719_;
goto v___jp_753_;
}
v___jp_753_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_758_ = lean_thunk_get_own(v_children_752_);
lean_dec_ref(v_children_752_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v___x_758_);
v___x_761_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec(v___x_758_);
lean_dec_ref(v_f_715_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_s_754_);
lean_ctor_set(v___x_762_, 1, v___y_755_);
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___y_757_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_760_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(v_f_715_, v___x_758_, v___x_766_, v___x_767_, v_s_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___x_758_);
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(lean_object* v_f_778_, lean_object* v_as_779_, size_t v_i_780_, size_t v_stop_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_eq(v_i_780_, v_stop_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_array_uget_borrowed(v_as_779_, v_i_780_);
lean_inc_ref(v_f_778_);
lean_inc(v___x_788_);
v___x_789_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(v___x_788_, v_f_778_, v_b_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v_fst_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_fst_791_ = lean_ctor_get(v_a_790_, 0);
if (lean_obj_tag(v_fst_791_) == 0)
{
lean_dec_ref(v_f_778_);
return v___x_789_;
}
else
{
lean_object* v_a_792_; lean_object* v_snd_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; size_t v___x_796_; size_t v___x_797_; 
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v_a_792_ = lean_ctor_get(v_fst_791_, 0);
lean_inc(v_a_792_);
v_snd_793_ = lean_ctor_get(v_a_790_, 1);
lean_inc(v_snd_793_);
lean_dec(v_a_790_);
v_fst_794_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_fst_794_);
v_snd_795_ = lean_ctor_get(v_a_792_, 1);
lean_inc(v_snd_795_);
lean_dec(v_a_792_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_780_, v___x_796_);
v_i_780_ = v___x_797_;
v_b_782_ = v_fst_794_;
v___y_783_ = v_snd_795_;
v___y_785_ = v_snd_793_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_778_);
return v___x_789_;
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v_f_778_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_b_782_);
lean_ctor_set(v___x_799_, 1, v___y_783_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___y_785_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_f_803_, lean_object* v_as_804_, lean_object* v_i_805_, lean_object* v_stop_806_, lean_object* v_b_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
size_t v_i_boxed_812_; size_t v_stop_boxed_813_; lean_object* v_res_814_; 
v_i_boxed_812_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_stop_boxed_813_ = lean_unbox_usize(v_stop_806_);
lean_dec(v_stop_806_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(v_f_803_, v_as_804_, v_i_boxed_812_, v_stop_boxed_813_, v_b_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_as_804_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_t_815_, lean_object* v_f_816_, lean_object* v_init_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(v_t_815_, v_f_816_, v_init_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg(lean_object* v_t_823_, lean_object* v_f_824_, lean_object* v_init_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_tree_830_; lean_object* v___x_831_; 
v_tree_830_ = lean_ctor_get(v_t_823_, 1);
lean_inc_ref(v_tree_830_);
lean_dec_ref(v_t_823_);
v___x_831_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(v_tree_830_, v_f_824_, v_init_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_t_832_, lean_object* v_f_833_, lean_object* v_init_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg(v_t_832_, v_f_833_, v_init_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0(lean_object* v_f_840_, lean_object* v_x_841_, lean_object* v_n_842_, lean_object* v_v_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
lean_inc_ref(v___y_845_);
v___x_848_ = lean_apply_6(v_f_840_, v_n_842_, v_v_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0___boxed(lean_object* v_f_849_, lean_object* v_x_850_, lean_object* v_n_851_, lean_object* v_v_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0(v_f_849_, v_x_850_, v_n_851_, v_v_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_t_858_, lean_object* v_f_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___f_864_ = lean_alloc_closure((void*)(l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_864_, 0, v_f_859_);
v___x_865_ = lean_box(0);
v___x_866_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg(v_t_858_, v___f_864_, v___x_865_, v___y_860_, v___y_861_, v___y_862_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_t_867_, lean_object* v_f_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_t_867_, v_f_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg(lean_object* v_f_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_i_877_, lean_object* v_acc_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_get_size(v_keys_875_);
v___x_884_ = lean_nat_dec_lt(v_i_877_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_i_877_);
lean_dec_ref(v_f_874_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_acc_878_);
lean_ctor_set(v___x_885_, 1, v___y_879_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___y_881_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v_k_889_; lean_object* v_v_890_; lean_object* v___x_891_; 
v_k_889_ = lean_array_fget_borrowed(v_keys_875_, v_i_877_);
v_v_890_ = lean_array_fget_borrowed(v_vals_876_, v_i_877_);
lean_inc_ref(v_f_874_);
lean_inc_ref(v___y_880_);
lean_inc(v_v_890_);
lean_inc(v_k_889_);
v___x_891_ = lean_apply_7(v_f_874_, v_acc_878_, v_k_889_, v_v_890_, v___y_879_, v___y_880_, v___y_881_, lean_box(0));
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_fst_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
v_fst_893_ = lean_ctor_get(v_a_892_, 0);
if (lean_obj_tag(v_fst_893_) == 0)
{
lean_dec(v_a_892_);
lean_dec(v_i_877_);
lean_dec_ref(v_f_874_);
return v___x_891_;
}
else
{
lean_object* v_a_894_; lean_object* v_snd_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref_known(v___x_891_, 1);
v_a_894_ = lean_ctor_get(v_fst_893_, 0);
lean_inc(v_a_894_);
v_snd_895_ = lean_ctor_get(v_a_892_, 1);
lean_inc(v_snd_895_);
lean_dec(v_a_892_);
v_fst_896_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_fst_896_);
v_snd_897_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_snd_897_);
lean_dec(v_a_894_);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_i_877_, v___x_898_);
lean_dec(v_i_877_);
v_i_877_ = v___x_899_;
v_acc_878_ = v_fst_896_;
v___y_879_ = v_snd_897_;
v___y_881_ = v_snd_895_;
goto _start;
}
}
else
{
lean_dec(v_i_877_);
lean_dec_ref(v_f_874_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_f_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_acc_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg(v_f_901_, v_keys_902_, v_vals_903_, v_i_904_, v_acc_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_vals_903_);
lean_dec_ref(v_keys_902_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg(lean_object* v_f_911_, lean_object* v_as_912_, size_t v_i_913_, size_t v_stop_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v_snd_923_; lean_object* v___y_928_; uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_eq(v_i_913_, v_stop_914_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
v___x_936_ = lean_array_uget_borrowed(v_as_912_, v_i_913_);
switch(lean_obj_tag(v___x_936_))
{
case 0:
{
lean_object* v_key_937_; lean_object* v_val_938_; lean_object* v___x_939_; 
v_key_937_ = lean_ctor_get(v___x_936_, 0);
v_val_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_f_911_);
lean_inc_ref(v___y_917_);
lean_inc(v_val_938_);
lean_inc(v_key_937_);
v___x_939_ = lean_apply_7(v_f_911_, v_b_915_, v_key_937_, v_val_938_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
v___y_928_ = v___x_939_;
goto v___jp_927_;
}
case 1:
{
lean_object* v_node_940_; lean_object* v___x_941_; 
v_node_940_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_node_940_);
lean_inc_ref(v_f_911_);
v___x_941_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v_f_911_, v_node_940_, v_b_915_, v___y_916_, v___y_917_, v___y_918_);
v___y_928_ = v___x_941_;
goto v___jp_927_;
}
default: 
{
v_fst_921_ = v_b_915_;
v_snd_922_ = v___y_916_;
v_snd_923_ = v___y_918_;
goto v___jp_920_;
}
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_f_911_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_b_915_);
lean_ctor_set(v___x_942_, 1, v___y_916_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___y_918_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
v___jp_920_:
{
size_t v___x_924_; size_t v___x_925_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_913_, v___x_924_);
v_i_913_ = v___x_925_;
v_b_915_ = v_fst_921_;
v___y_916_ = v_snd_922_;
v___y_918_ = v_snd_923_;
goto _start;
}
v___jp_927_:
{
if (lean_obj_tag(v___y_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_fst_930_; 
v_a_929_ = lean_ctor_get(v___y_928_, 0);
v_fst_930_ = lean_ctor_get(v_a_929_, 0);
if (lean_obj_tag(v_fst_930_) == 0)
{
lean_dec_ref(v_f_911_);
return v___y_928_;
}
else
{
lean_object* v_a_931_; lean_object* v_snd_932_; lean_object* v_fst_933_; lean_object* v_snd_934_; 
lean_inc(v_a_929_);
lean_dec_ref_known(v___y_928_, 1);
v_a_931_ = lean_ctor_get(v_fst_930_, 0);
lean_inc(v_a_931_);
v_snd_932_ = lean_ctor_get(v_a_929_, 1);
lean_inc(v_snd_932_);
lean_dec(v_a_929_);
v_fst_933_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_fst_933_);
v_snd_934_ = lean_ctor_get(v_a_931_, 1);
lean_inc(v_snd_934_);
lean_dec(v_a_931_);
v_fst_921_ = v_fst_933_;
v_snd_922_ = v_snd_934_;
v_snd_923_ = v_snd_932_;
goto v___jp_920_;
}
}
else
{
lean_dec_ref(v_f_911_);
return v___y_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_f_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_object* v_es_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_969_; 
v_es_953_ = lean_ctor_get(v_x_947_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_947_);
if (v_isSharedCheck_969_ == 0)
{
v___x_955_ = v_x_947_;
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_es_953_);
lean_dec(v_x_947_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_array_get_size(v_es_953_);
v___x_959_ = lean_nat_dec_lt(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec_ref(v_es_953_);
lean_dec_ref(v_f_946_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_x_948_);
lean_ctor_set(v___x_960_, 1, v___y_949_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
lean_ctor_set(v___x_955_, 0, v___x_960_);
v___x_962_ = v___x_955_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_965_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___y_951_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_955_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_958_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg(v_f_946_, v_es_953_, v___x_966_, v___x_967_, v_x_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec_ref(v_es_953_);
return v___x_968_;
}
}
}
else
{
lean_object* v_ks_970_; lean_object* v_vs_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_ks_970_ = lean_ctor_get(v_x_947_, 0);
lean_inc_ref(v_ks_970_);
v_vs_971_ = lean_ctor_get(v_x_947_, 1);
lean_inc_ref(v_vs_971_);
lean_dec_ref_known(v_x_947_, 2);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg(v_f_946_, v_ks_970_, v_vs_971_, v___x_972_, v_x_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec_ref(v_vs_971_);
lean_dec_ref(v_ks_970_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_f_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v_f_974_, v_x_975_, v_x_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_f_982_, lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; lean_object* v_res_993_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg(v_f_982_, v_as_983_, v_i_boxed_991_, v_stop_boxed_992_, v_b_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_as_983_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
lean_inc_ref(v___y_999_);
v___x_1002_ = lean_apply_6(v_f_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, lean_box(0));
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_1003_, v_x_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_1012_, lean_object* v_f_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1018_, 0, v_f_1013_);
v___x_1019_ = lean_box(0);
v___x_1020_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v___f_1018_, v_map_1012_, v___x_1019_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_1021_, lean_object* v_f_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_1021_, v_f_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_map_1028_, lean_object* v_f_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_map_u2081_1034_; lean_object* v_map_u2082_1035_; lean_object* v___x_1036_; 
v_map_u2081_1034_ = lean_ctor_get(v_map_1028_, 0);
lean_inc_ref(v_map_u2081_1034_);
v_map_u2082_1035_ = lean_ctor_get(v_map_1028_, 1);
lean_inc_ref(v_map_u2082_1035_);
lean_dec_ref(v_map_1028_);
lean_inc_ref(v_f_1029_);
v___x_1036_ = l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_map_u2081_1034_, v_f_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v_fst_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_fst_1038_ = lean_ctor_get(v_a_1037_, 0);
if (lean_obj_tag(v_fst_1038_) == 0)
{
lean_dec_ref(v_map_u2082_1035_);
lean_dec_ref(v_f_1029_);
return v___x_1036_;
}
else
{
lean_object* v_a_1039_; lean_object* v_snd_1040_; lean_object* v_snd_1041_; lean_object* v___x_1042_; 
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v_a_1039_ = lean_ctor_get(v_fst_1038_, 0);
lean_inc(v_a_1039_);
v_snd_1040_ = lean_ctor_get(v_a_1037_, 1);
lean_inc(v_snd_1040_);
lean_dec(v_a_1037_);
v_snd_1041_ = lean_ctor_get(v_a_1039_, 1);
lean_inc(v_snd_1041_);
lean_dec(v_a_1039_);
v___x_1042_ = l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_1035_, v_f_1029_, v_snd_1041_, v___y_1031_, v_snd_1040_);
return v___x_1042_;
}
}
else
{
lean_dec_ref(v_map_u2082_1035_);
lean_dec_ref(v_f_1029_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_map_1043_, lean_object* v_f_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5(v_map_1043_, v_f_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
uint8_t v___x_1052_; 
v___x_1052_ = 0;
return v___x_1052_;
}
else
{
lean_object* v_head_1053_; lean_object* v_tail_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_head_1053_ = lean_ctor_get(v_x_1051_, 0);
v_tail_1054_ = lean_ctor_get(v_x_1051_, 1);
v___x_1055_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_1056_ = lean_string_dec_eq(v_head_1053_, v___x_1055_);
if (v___x_1056_ == 0)
{
v_x_1051_ = v_tail_1054_;
goto _start;
}
else
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_1058_);
lean_dec(v_x_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object* v_env_1062_, lean_object* v_cliOptions_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___f_1089_; lean_object* v_recursorMap_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___f_1089_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_1090_ = lean_box(1);
v___x_1091_ = l_Lean_Environment_constants(v_env_1062_);
v___x_1092_ = l_Lean_ConstMap_forM___at___00LeanExport_initState_spec__5(v___x_1091_, v___f_1089_, v_recursorMap_1090_, v_a_1064_, v_a_1065_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v_fst_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v_fst_1094_ = lean_ctor_get(v_a_1093_, 0);
if (lean_obj_tag(v_fst_1094_) == 0)
{
lean_object* v_snd_1095_; lean_object* v_a_1096_; 
lean_inc_ref(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_a_1093_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_a_1093_);
v_a_1096_ = lean_ctor_get(v_fst_1094_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v_fst_1094_, 1);
v_fst_1068_ = v_a_1096_;
v_snd_1069_ = v_snd_1095_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1097_; lean_object* v_snd_1098_; lean_object* v_snd_1099_; 
v_a_1097_ = lean_ctor_get(v_fst_1094_, 0);
lean_inc(v_a_1097_);
v_snd_1098_ = lean_ctor_get(v_a_1093_, 1);
lean_inc(v_snd_1098_);
lean_dec(v_a_1093_);
v_snd_1099_ = lean_ctor_get(v_a_1097_, 1);
lean_inc(v_snd_1099_);
lean_dec(v_a_1097_);
v_fst_1068_ = v_snd_1099_;
v_snd_1069_ = v_snd_1098_;
goto v___jp_1067_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1092_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1092_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_1067_:
{
lean_object* v_visitedNames_1070_; lean_object* v_visitedLevels_1071_; lean_object* v_visitedExprs_1072_; lean_object* v_visitedConstants_1073_; lean_object* v_noMDataExprs_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1087_; 
v_visitedNames_1070_ = lean_ctor_get(v_snd_1069_, 0);
v_visitedLevels_1071_ = lean_ctor_get(v_snd_1069_, 1);
v_visitedExprs_1072_ = lean_ctor_get(v_snd_1069_, 2);
v_visitedConstants_1073_ = lean_ctor_get(v_snd_1069_, 3);
v_noMDataExprs_1074_ = lean_ctor_get(v_snd_1069_, 4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_snd_1069_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_snd_1069_, 5);
lean_dec(v_unused_1088_);
v___x_1076_ = v_snd_1069_;
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_noMDataExprs_1074_);
lean_inc(v_visitedConstants_1073_);
lean_inc(v_visitedExprs_1072_);
lean_inc(v_visitedLevels_1071_);
lean_inc(v_visitedNames_1070_);
lean_dec(v_snd_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1083_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_1063_);
v___x_1080_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_1063_);
v___x_1081_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_1063_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 5, v_fst_1068_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_visitedNames_1070_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_visitedLevels_1071_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_visitedExprs_1072_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_visitedConstants_1073_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_noMDataExprs_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 5, v_fst_1068_);
v___x_1083_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*6, v___x_1079_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*6 + 1, v___x_1080_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*6 + 2, v___x_1081_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1078_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_1108_, lean_object* v_cliOptions_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_LeanExport_initState(v_env_1108_, v_cliOptions_1109_, v_a_1110_, v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_cliOptions_1109_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_1114_, lean_object* v_k_1115_, lean_object* v_t_1116_, lean_object* v_hl_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_1114_, v_k_1115_, v_t_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_1119_, lean_object* v_as_1120_, lean_object* v_as_x27_1121_, lean_object* v_b_1122_, lean_object* v_a_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_1119_, v_as_x27_1121_, v_b_1122_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_1128_, lean_object* v_as_1129_, lean_object* v_as_x27_1130_, lean_object* v_b_1131_, lean_object* v_a_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_1128_, v_as_1129_, v_as_x27_1130_, v_b_1131_, v_a_1132_, v___y_1133_, v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v_as_x27_1130_);
lean_dec(v_as_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b1_1137_, lean_object* v_t_1138_, lean_object* v_f_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_t_1138_, v_f_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_t_1146_, lean_object* v_f_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b1_1145_, v_t_1146_, v_f_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_1153_, lean_object* v_map_1154_, lean_object* v_f_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_1154_, v_f_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_map_1162_, lean_object* v_f_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1161_, v_map_1162_, v_f_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03c3_1170_, lean_object* v_t_1171_, lean_object* v_f_1172_, lean_object* v_init_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___redArg(v_t_1171_, v_f_1172_, v_init_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03c3_1180_, lean_object* v_t_1181_, lean_object* v_f_1182_, lean_object* v_init_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6(v_00_u03b1_1179_, v_00_u03c3_1180_, v_t_1181_, v_f_1182_, v_init_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___redArg(lean_object* v_map_1189_, lean_object* v_f_1190_, lean_object* v_init_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v_f_1190_, v_map_1189_, v_init_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_map_1197_, lean_object* v_f_1198_, lean_object* v_init_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___redArg(v_map_1197_, v_f_1198_, v_init_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8(lean_object* v_00_u03c3_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_map_1207_, lean_object* v_f_1208_, lean_object* v_init_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v_f_1208_, v_map_1207_, v_init_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03c3_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_map_1217_, lean_object* v_f_1218_, lean_object* v_init_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8(v_00_u03c3_1215_, v_00_u03b2_1216_, v_map_1217_, v_f_1218_, v_init_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b1_1225_, lean_object* v_00_u03c3_1226_, lean_object* v_t_1227_, lean_object* v_f_1228_, lean_object* v_init_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___redArg(v_t_1227_, v_f_1228_, v_init_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03c3_1236_, lean_object* v_t_1237_, lean_object* v_f_1238_, lean_object* v_init_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7(v_00_u03b1_1235_, v_00_u03c3_1236_, v_t_1237_, v_f_1238_, v_init_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03c3_1245_, lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_f_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___redArg(v_f_1248_, v_x_1249_, v_x_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03c3_1256_, lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_f_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10(v_00_u03c3_1256_, v_00_u03b1_1257_, v_00_u03b2_1258_, v_f_1259_, v_x_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03c3_1268_, lean_object* v_t_1269_, lean_object* v_f_1270_, lean_object* v_init_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___redArg(v_t_1269_, v_f_1270_, v_init_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03c3_1278_, lean_object* v_t_1279_, lean_object* v_f_1280_, lean_object* v_init_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9(v_00_u03b1_1277_, v_00_u03c3_1278_, v_t_1279_, v_f_1280_, v_init_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03c3_1288_, lean_object* v_f_1289_, lean_object* v_as_1290_, size_t v_i_1291_, size_t v_stop_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___redArg(v_f_1289_, v_as_1290_, v_i_1291_, v_stop_1292_, v_b_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03c3_1300_, lean_object* v_f_1301_, lean_object* v_as_1302_, lean_object* v_i_1303_, lean_object* v_stop_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_i_boxed_1310_; size_t v_stop_boxed_1311_; lean_object* v_res_1312_; 
v_i_boxed_1310_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_stop_boxed_1311_ = lean_unbox_usize(v_stop_1304_);
lean_dec(v_stop_1304_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__10(v_00_u03b1_1299_, v_00_u03c3_1300_, v_f_1301_, v_as_1302_, v_i_boxed_1310_, v_stop_boxed_1311_, v_b_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v_as_1302_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_00_u03c3_1315_, lean_object* v_f_1316_, lean_object* v_as_1317_, size_t v_i_1318_, size_t v_stop_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___redArg(v_f_1316_, v_as_1317_, v_i_1318_, v_stop_1319_, v_b_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_00_u03c3_1328_, lean_object* v_f_1329_, lean_object* v_as_1330_, lean_object* v_i_1331_, lean_object* v_stop_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
size_t v_i_boxed_1338_; size_t v_stop_boxed_1339_; lean_object* v_res_1340_; 
v_i_boxed_1338_ = lean_unbox_usize(v_i_1331_);
lean_dec(v_i_1331_);
v_stop_boxed_1339_ = lean_unbox_usize(v_stop_1332_);
lean_dec(v_stop_1332_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__13(v_00_u03b1_1326_, v_00_u03b2_1327_, v_00_u03c3_1328_, v_f_1329_, v_as_1330_, v_i_boxed_1338_, v_stop_boxed_1339_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_as_1330_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14(lean_object* v_00_u03c3_1341_, lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_f_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_acc_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___redArg(v_f_1344_, v_keys_1345_, v_vals_1346_, v_i_1348_, v_acc_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03c3_1355_, lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_f_1358_, lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_heq_1361_, lean_object* v_i_1362_, lean_object* v_acc_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__8_spec__10_spec__14(v_00_u03c3_1355_, v_00_u03b1_1356_, v_00_u03b2_1357_, v_f_1358_, v_keys_1359_, v_vals_1360_, v_heq_1361_, v_i_1362_, v_acc_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v_vals_1360_);
lean_dec_ref(v_keys_1359_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03c3_1370_, lean_object* v_f_1371_, lean_object* v_as_1372_, size_t v_i_1373_, size_t v_stop_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___redArg(v_f_1371_, v_as_1372_, v_i_1373_, v_stop_1374_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_00_u03c3_1382_, lean_object* v_f_1383_, lean_object* v_as_1384_, lean_object* v_i_1385_, lean_object* v_stop_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
size_t v_i_boxed_1392_; size_t v_stop_boxed_1393_; lean_object* v_res_1394_; 
v_i_boxed_1392_ = lean_unbox_usize(v_i_1385_);
lean_dec(v_i_1385_);
v_stop_boxed_1393_ = lean_unbox_usize(v_stop_1386_);
lean_dec(v_stop_1386_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ConstTrie_foldlM___at___00__private_Lean_ConstTrie_0__Lean_ImportedTree_foldlM___at___00Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_forM___at___00Lean_ConstMap_forM___at___00LeanExport_initState_spec__5_spec__5_spec__6_spec__7_spec__9_spec__11(v_00_u03b1_1381_, v_00_u03c3_1382_, v_f_1383_, v_as_1384_, v_i_boxed_1392_, v_stop_boxed_1393_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_as_1384_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_x_1398_, lean_object* v_namespaced_1399_, lean_object* v_getM_1400_, lean_object* v_setM_1401_, lean_object* v_rec_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_getM_1400_);
lean_inc_ref(v_a_1404_);
v___x_1406_ = lean_apply_1(v_getM_1400_, v_a_1404_);
lean_inc(v_x_1398_);
lean_inc_ref(v_inst_1396_);
lean_inc_ref(v_inst_1397_);
v___x_1407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1397_, v_inst_1396_, v___x_1406_, v_x_1398_);
lean_dec_ref(v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_rec_1402_);
lean_dec_ref(v_setM_1401_);
lean_dec_ref(v_getM_1400_);
lean_dec_ref(v_namespaced_1399_);
lean_dec(v_x_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec_ref(v_inst_1396_);
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_val_1408_);
lean_ctor_set(v___x_1412_, 1, v_a_1404_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v___f_1417_; lean_object* v___x_1418_; 
lean_dec(v___x_1407_);
v___f_1417_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1403_);
v___x_1418_ = lean_apply_3(v_rec_1402_, v_a_1403_, v_a_1404_, lean_box(0));
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1453_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v_fst_1420_ = lean_ctor_get(v_a_1419_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1419_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_a_1419_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1423_ = v_a_1419_;
v_isShared_1424_ = v_isSharedCheck_1453_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_inc(v_fst_1420_);
lean_dec(v_a_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1453_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v_size_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_inc(v_snd_1421_);
v___x_1425_ = lean_apply_1(v_getM_1400_, v_snd_1421_);
v_size_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc_n(v_size_1426_, 2);
v___x_1427_ = l_Lean_JsonNumber_fromNat(v_size_1426_);
v___x_1428_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = l_Lean_Json_setObjVal_x21(v_fst_1420_, v_namespaced_1399_, v___x_1428_);
v___x_1430_ = l_Lean_Json_compress(v___x_1429_);
v___x_1431_ = l_IO_println___redArg(v___f_1417_, v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1443_; 
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v___x_1431_, 0);
lean_dec(v_unused_1444_);
v___x_1433_ = v___x_1431_;
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1431_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_inc(v_size_1426_);
v___x_1435_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1397_, v_inst_1396_, v___x_1425_, v_x_1398_, v_size_1426_);
v___x_1436_ = lean_apply_2(v_setM_1401_, v_snd_1421_, v___x_1435_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1436_);
lean_ctor_set(v___x_1423_, 0, v_size_1426_);
v___x_1438_ = v___x_1423_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_size_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1438_);
v___x_1440_ = v___x_1433_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_size_1426_);
lean_dec_ref(v___x_1425_);
lean_del_object(v___x_1423_);
lean_dec(v_snd_1421_);
lean_dec_ref(v_setM_1401_);
lean_dec(v_x_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec_ref(v_inst_1396_);
v_a_1445_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1431_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1431_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_setM_1401_);
lean_dec_ref(v_getM_1400_);
lean_dec_ref(v_namespaced_1399_);
lean_dec(v_x_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec_ref(v_inst_1396_);
v_a_1454_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1418_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1418_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_x_1464_, lean_object* v_namespaced_1465_, lean_object* v_getM_1466_, lean_object* v_setM_1467_, lean_object* v_rec_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1462_, v_inst_1463_, v_x_1464_, v_namespaced_1465_, v_getM_1466_, v_setM_1467_, v_rec_1468_, v_a_1469_, v_a_1470_);
lean_dec_ref(v_a_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_x_1476_, lean_object* v_namespaced_1477_, lean_object* v_getM_1478_, lean_object* v_setM_1479_, lean_object* v_rec_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc_ref(v_getM_1478_);
lean_inc_ref(v_a_1482_);
v___x_1484_ = lean_apply_1(v_getM_1478_, v_a_1482_);
lean_inc(v_x_1476_);
lean_inc_ref(v_inst_1474_);
lean_inc_ref(v_inst_1475_);
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1475_, v_inst_1474_, v___x_1484_, v_x_1476_);
lean_dec_ref(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_rec_1480_);
lean_dec_ref(v_setM_1479_);
lean_dec_ref(v_getM_1478_);
lean_dec_ref(v_namespaced_1477_);
lean_dec(v_x_1476_);
lean_dec_ref(v_inst_1475_);
lean_dec_ref(v_inst_1474_);
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_val_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_val_1486_);
lean_ctor_set(v___x_1490_, 1, v_a_1482_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
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
lean_object* v___f_1495_; lean_object* v___x_1496_; 
lean_dec(v___x_1485_);
v___f_1495_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1481_);
v___x_1496_ = lean_apply_3(v_rec_1480_, v_a_1481_, v_a_1482_, lean_box(0));
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v_fst_1498_; lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1531_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v_fst_1498_ = lean_ctor_get(v_a_1497_, 0);
v_snd_1499_ = lean_ctor_get(v_a_1497_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1501_ = v_a_1497_;
v_isShared_1502_ = v_isSharedCheck_1531_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_inc(v_fst_1498_);
lean_dec(v_a_1497_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1531_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v_size_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_inc(v_snd_1499_);
v___x_1503_ = lean_apply_1(v_getM_1478_, v_snd_1499_);
v_size_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_n(v_size_1504_, 2);
v___x_1505_ = l_Lean_JsonNumber_fromNat(v_size_1504_);
v___x_1506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
v___x_1507_ = l_Lean_Json_setObjVal_x21(v_fst_1498_, v_namespaced_1477_, v___x_1506_);
v___x_1508_ = l_Lean_Json_compress(v___x_1507_);
v___x_1509_ = l_IO_println___redArg(v___f_1495_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1509_, 0);
lean_dec(v_unused_1522_);
v___x_1511_ = v___x_1509_;
v_isShared_1512_ = v_isSharedCheck_1521_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v___x_1509_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1521_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_inc(v_size_1504_);
v___x_1513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1475_, v_inst_1474_, v___x_1503_, v_x_1476_, v_size_1504_);
v___x_1514_ = lean_apply_2(v_setM_1479_, v_snd_1499_, v___x_1513_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1514_);
lean_ctor_set(v___x_1501_, 0, v_size_1504_);
v___x_1516_ = v___x_1501_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_size_1504_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1516_);
v___x_1518_ = v___x_1511_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_size_1504_);
lean_dec_ref(v___x_1503_);
lean_del_object(v___x_1501_);
lean_dec(v_snd_1499_);
lean_dec_ref(v_setM_1479_);
lean_dec(v_x_1476_);
lean_dec_ref(v_inst_1475_);
lean_dec_ref(v_inst_1474_);
v_a_1523_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1509_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1509_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_setM_1479_);
lean_dec_ref(v_getM_1478_);
lean_dec_ref(v_namespaced_1477_);
lean_dec(v_x_1476_);
lean_dec_ref(v_inst_1475_);
lean_dec_ref(v_inst_1474_);
v_a_1532_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1496_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1496_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_x_1543_, lean_object* v_namespaced_1544_, lean_object* v_getM_1545_, lean_object* v_setM_1546_, lean_object* v_rec_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1540_, v_inst_1541_, v_inst_1542_, v_x_1543_, v_namespaced_1544_, v_getM_1545_, v_setM_1546_, v_rec_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1551_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_instMonadEIO___redArg();
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v___x_1423__overap_1571_; lean_object* v___x_1572_; 
v___x_1557_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1558_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1558_, 0, v___x_1557_);
v___f_1559_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1559_, 0, v___x_1557_);
v___f_1560_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1560_, 0, v___x_1557_);
v___f_1561_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1561_, 0, v___x_1557_);
v___x_1562_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1562_, 0, lean_box(0));
lean_closure_set(v___x_1562_, 1, lean_box(0));
lean_closure_set(v___x_1562_, 2, v___x_1557_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___f_1558_);
v___x_1564_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1564_, 0, lean_box(0));
lean_closure_set(v___x_1564_, 1, lean_box(0));
lean_closure_set(v___x_1564_, 2, v___x_1557_);
v___x_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
lean_ctor_set(v___x_1565_, 2, v___f_1559_);
lean_ctor_set(v___x_1565_, 3, v___f_1560_);
lean_ctor_set(v___x_1565_, 4, v___f_1561_);
v___x_1566_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1566_, 0, lean_box(0));
lean_closure_set(v___x_1566_, 1, lean_box(0));
lean_closure_set(v___x_1566_, 2, v___x_1557_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_box(0);
v___x_1569_ = l_instInhabitedOfMonad___redArg(v___x_1567_, v___x_1568_);
v___f_1570_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1570_, 0, v___x_1569_);
v___x_1423__overap_1571_ = lean_panic_fn_borrowed(v___f_1570_, v_msg_1553_);
lean_dec_ref(v___f_1570_);
lean_inc_ref(v___y_1554_);
v___x_1572_ = lean_apply_3(v___x_1423__overap_1571_, v___y_1554_, v___y_1555_, lean_box(0));
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1573_, v___y_1574_, v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v_key_1581_; lean_object* v_value_1582_; lean_object* v_tail_1583_; uint8_t v___x_1584_; 
v_key_1581_ = lean_ctor_get(v_x_1579_, 0);
v_value_1582_ = lean_ctor_get(v_x_1579_, 1);
v_tail_1583_ = lean_ctor_get(v_x_1579_, 2);
v___x_1584_ = lean_name_eq(v_key_1581_, v_a_1578_);
if (v___x_1584_ == 0)
{
v_x_1579_ = v_tail_1583_;
goto _start;
}
else
{
lean_object* v___x_1586_; 
lean_inc(v_value_1582_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_value_1582_);
return v___x_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec(v_a_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_buckets_1592_; lean_object* v___x_1593_; uint64_t v___y_1595_; 
v_buckets_1592_ = lean_ctor_get(v_m_1590_, 1);
v___x_1593_ = lean_array_get_size(v_buckets_1592_);
if (lean_obj_tag(v_a_1591_) == 0)
{
uint64_t v___x_1609_; 
v___x_1609_ = 1723ULL;
v___y_1595_ = v___x_1609_;
goto v___jp_1594_;
}
else
{
uint64_t v_hash_1610_; 
v_hash_1610_ = lean_ctor_get_uint64(v_a_1591_, sizeof(void*)*2);
v___y_1595_ = v_hash_1610_;
goto v___jp_1594_;
}
v___jp_1594_:
{
uint64_t v___x_1596_; uint64_t v___x_1597_; uint64_t v_fold_1598_; uint64_t v___x_1599_; uint64_t v___x_1600_; uint64_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1596_ = 32ULL;
v___x_1597_ = lean_uint64_shift_right(v___y_1595_, v___x_1596_);
v_fold_1598_ = lean_uint64_xor(v___y_1595_, v___x_1597_);
v___x_1599_ = 16ULL;
v___x_1600_ = lean_uint64_shift_right(v_fold_1598_, v___x_1599_);
v___x_1601_ = lean_uint64_xor(v_fold_1598_, v___x_1600_);
v___x_1602_ = lean_uint64_to_usize(v___x_1601_);
v___x_1603_ = lean_usize_of_nat(v___x_1593_);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_sub(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_usize_land(v___x_1602_, v___x_1605_);
v___x_1607_ = lean_array_uget_borrowed(v_buckets_1592_, v___x_1606_);
v___x_1608_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1591_, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_m_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v_putStr_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_get_stdout();
v_putStr_1617_ = lean_ctor_get(v___x_1616_, 4);
lean_inc_ref(v_putStr_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_apply_2(v_putStr_1617_, v_s_1614_, lean_box(0));
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1622_){
_start:
{
uint32_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 10;
v___x_1625_ = lean_string_push(v_s_1622_, v___x_1624_);
v___x_1626_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1627_);
return v_res_1629_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1634_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1635_ = lean_unsigned_to_nat(18u);
v___x_1636_ = lean_unsigned_to_nat(114u);
v___x_1637_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1638_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1639_ = l_mkPanicMessageWithDecl(v___x_1638_, v___x_1637_, v___x_1636_, v___x_1635_, v___x_1634_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_visitedNames_1648_; lean_object* v___x_1649_; 
v_visitedNames_1648_ = lean_ctor_get(v_a_1646_, 0);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1648_, v_n_1644_);
if (lean_obj_tag(v___x_1649_) == 1)
{
lean_object* v_val_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_n_1644_);
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_val_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_val_1650_);
lean_ctor_set(v___x_1654_, 1, v_a_1646_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
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
lean_object* v___x_1659_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; 
lean_dec(v___x_1649_);
v___x_1659_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1644_))
{
case 0:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1704_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1703_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v_fst_1706_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_fst_1706_);
v_snd_1707_ = lean_ctor_get(v_a_1705_, 1);
lean_inc(v_snd_1707_);
lean_dec(v_a_1705_);
v_fst_1661_ = v_fst_1706_;
v_snd_1662_ = v_snd_1707_;
goto v___jp_1660_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1704_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1704_);
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
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
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
}
case 1:
{
lean_object* v_pre_1716_; lean_object* v_str_1717_; lean_object* v___x_1718_; 
v_pre_1716_ = lean_ctor_get(v_n_1644_, 0);
v_str_1717_ = lean_ctor_get(v_n_1644_, 1);
lean_inc(v_pre_1716_);
v___x_1718_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1716_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1747_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1747_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1747_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1746_; 
v_fst_1723_ = lean_ctor_get(v_a_1719_, 0);
v_snd_1724_ = lean_ctor_get(v_a_1719_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1719_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1726_ = v_a_1719_;
v_isShared_1727_ = v_isSharedCheck_1746_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_a_1719_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1746_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1728_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1729_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1730_ = l_Lean_JsonNumber_fromNat(v_fst_1723_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 2);
lean_ctor_set(v___x_1721_, 0, v___x_1730_);
v___x_1732_ = v___x_1721_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1732_);
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc_ref(v_str_1717_);
v___x_1735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_str_1717_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1728_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_Json_mkObj(v___x_1739_);
lean_dec_ref_known(v___x_1739_, 2);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1728_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1737_);
v___x_1743_ = l_Lean_Json_mkObj(v___x_1742_);
lean_dec_ref_known(v___x_1742_, 2);
v_fst_1661_ = v___x_1743_;
v_snd_1662_ = v_snd_1724_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1644_, 2);
return v___x_1718_;
}
}
default: 
{
lean_object* v_pre_1748_; lean_object* v_i_1749_; lean_object* v___x_1750_; 
v_pre_1748_ = lean_ctor_get(v_n_1644_, 0);
v_i_1749_ = lean_ctor_get(v_n_1644_, 1);
lean_inc(v_pre_1748_);
v___x_1750_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1748_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1781_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1781_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1781_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_fst_1755_; lean_object* v_snd_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1780_; 
v_fst_1755_ = lean_ctor_get(v_a_1751_, 0);
v_snd_1756_ = lean_ctor_get(v_a_1751_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1758_ = v_a_1751_;
v_isShared_1759_ = v_isSharedCheck_1780_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snd_1756_);
lean_inc(v_fst_1755_);
lean_dec(v_a_1751_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1780_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1760_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1761_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1762_ = l_Lean_JsonNumber_fromNat(v_fst_1755_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 2);
lean_ctor_set(v___x_1753_, 0, v___x_1762_);
v___x_1764_ = v___x_1753_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v___x_1764_);
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1766_ = v___x_1758_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1767_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1749_);
v___x_1768_ = l_Lean_JsonNumber_fromNat(v_i_1749_);
v___x_1769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1767_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1766_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_Json_mkObj(v___x_1773_);
lean_dec_ref_known(v___x_1773_, 2);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1760_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1771_);
v___x_1777_ = l_Lean_Json_mkObj(v___x_1776_);
lean_dec_ref_known(v___x_1776_, 2);
v_fst_1661_ = v___x_1777_;
v_snd_1662_ = v_snd_1756_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1644_, 2);
return v___x_1750_;
}
}
}
v___jp_1660_:
{
lean_object* v_visitedNames_1663_; lean_object* v_visitedLevels_1664_; lean_object* v_visitedExprs_1665_; lean_object* v_visitedConstants_1666_; lean_object* v_noMDataExprs_1667_; uint8_t v_exportMData_1668_; uint8_t v_exportUnsafe_1669_; uint8_t v_ignoreMissing_1670_; lean_object* v_recursorMap_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1702_; 
v_visitedNames_1663_ = lean_ctor_get(v_snd_1662_, 0);
v_visitedLevels_1664_ = lean_ctor_get(v_snd_1662_, 1);
v_visitedExprs_1665_ = lean_ctor_get(v_snd_1662_, 2);
v_visitedConstants_1666_ = lean_ctor_get(v_snd_1662_, 3);
v_noMDataExprs_1667_ = lean_ctor_get(v_snd_1662_, 4);
v_exportMData_1668_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6);
v_exportUnsafe_1669_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6 + 1);
v_ignoreMissing_1670_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6 + 2);
v_recursorMap_1671_ = lean_ctor_get(v_snd_1662_, 5);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_snd_1662_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1673_ = v_snd_1662_;
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_recursorMap_1671_);
lean_inc(v_noMDataExprs_1667_);
lean_inc(v_visitedConstants_1666_);
lean_inc(v_visitedExprs_1665_);
lean_inc(v_visitedLevels_1664_);
lean_inc(v_visitedNames_1663_);
lean_dec(v_snd_1662_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_size_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_size_1675_ = lean_ctor_get(v_visitedNames_1663_, 0);
lean_inc_n(v_size_1675_, 2);
v___x_1676_ = l_Lean_JsonNumber_fromNat(v_size_1675_);
v___x_1677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = l_Lean_Json_setObjVal_x21(v_fst_1661_, v___x_1659_, v___x_1677_);
v___x_1679_ = l_Lean_Json_compress(v___x_1678_);
v___x_1680_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1692_; 
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1680_, 0);
lean_dec(v_unused_1693_);
v___x_1682_ = v___x_1680_;
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
else
{
lean_dec(v___x_1680_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_inc(v_size_1675_);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1663_, v_n_1644_, v_size_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1684_);
v___x_1686_ = v___x_1673_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_visitedLevels_1664_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_visitedExprs_1665_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_visitedConstants_1666_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_noMDataExprs_1667_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v_recursorMap_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6, v_exportMData_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6 + 1, v_exportUnsafe_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6 + 2, v_ignoreMissing_1670_);
v___x_1686_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_size_1675_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1687_);
v___x_1689_ = v___x_1682_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_size_1675_);
lean_del_object(v___x_1673_);
lean_dec(v_recursorMap_1671_);
lean_dec_ref(v_noMDataExprs_1667_);
lean_dec_ref(v_visitedConstants_1666_);
lean_dec_ref(v_visitedExprs_1665_);
lean_dec_ref(v_visitedLevels_1664_);
lean_dec_ref(v_visitedNames_1663_);
lean_dec(v_n_1644_);
v_a_1694_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1680_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1680_);
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
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1782_, v_a_1783_, v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1787_, lean_object* v_m_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1788_, v_a_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1791_, lean_object* v_m_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1791_, v_m_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_m_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1795_, lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1796_, v_x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1799_, lean_object* v_a_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1799_, v_a_1800_, v_x_1801_);
lean_dec(v_x_1801_);
lean_dec(v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_box(0);
return v___x_1805_;
}
else
{
lean_object* v_key_1806_; lean_object* v_value_1807_; lean_object* v_tail_1808_; uint8_t v___x_1809_; 
v_key_1806_ = lean_ctor_get(v_x_1804_, 0);
v_value_1807_ = lean_ctor_get(v_x_1804_, 1);
v_tail_1808_ = lean_ctor_get(v_x_1804_, 2);
v___x_1809_ = lean_level_eq(v_key_1806_, v_a_1803_);
if (v___x_1809_ == 0)
{
v_x_1804_ = v_tail_1808_;
goto _start;
}
else
{
lean_object* v___x_1811_; 
lean_inc(v_value_1807_);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_value_1807_);
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1812_, v_x_1813_);
lean_dec(v_x_1813_);
lean_dec(v_a_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_buckets_1817_; lean_object* v___x_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; uint64_t v___x_1821_; uint64_t v_fold_1822_; uint64_t v___x_1823_; uint64_t v___x_1824_; uint64_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_buckets_1817_ = lean_ctor_get(v_m_1815_, 1);
v___x_1818_ = lean_array_get_size(v_buckets_1817_);
v___x_1819_ = l_Lean_Level_hash(v_a_1816_);
v___x_1820_ = 32ULL;
v___x_1821_ = lean_uint64_shift_right(v___x_1819_, v___x_1820_);
v_fold_1822_ = lean_uint64_xor(v___x_1819_, v___x_1821_);
v___x_1823_ = 16ULL;
v___x_1824_ = lean_uint64_shift_right(v_fold_1822_, v___x_1823_);
v___x_1825_ = lean_uint64_xor(v_fold_1822_, v___x_1824_);
v___x_1826_ = lean_uint64_to_usize(v___x_1825_);
v___x_1827_ = lean_usize_of_nat(v___x_1818_);
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_sub(v___x_1827_, v___x_1828_);
v___x_1830_ = lean_usize_land(v___x_1826_, v___x_1829_);
v___x_1831_ = lean_array_uget_borrowed(v_buckets_1817_, v___x_1830_);
v___x_1832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1816_, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_m_1833_);
return v_res_1835_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1842_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1843_ = lean_unsigned_to_nat(23u);
v___x_1844_ = lean_unsigned_to_nat(132u);
v___x_1845_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1846_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1847_ = l_mkPanicMessageWithDecl(v___x_1846_, v___x_1845_, v___x_1844_, v___x_1843_, v___x_1842_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_visitedLevels_1852_; lean_object* v___x_1853_; 
v_visitedLevels_1852_ = lean_ctor_get(v_a_1850_, 1);
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1852_, v_l_1848_);
if (lean_obj_tag(v___x_1853_) == 1)
{
lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_l_1848_);
v_val_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_val_1854_);
lean_ctor_set(v___x_1858_, 1, v_a_1850_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; 
lean_dec(v___x_1853_);
v___x_1863_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1848_))
{
case 1:
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v_l_1848_, 0);
lean_inc(v_a_1907_);
v___x_1908_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1907_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1930_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1930_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1930_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1929_; 
v_fst_1913_ = lean_ctor_get(v_a_1909_, 0);
v_snd_1914_ = lean_ctor_get(v_a_1909_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_a_1909_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1916_ = v_a_1909_;
v_isShared_1917_ = v_isSharedCheck_1929_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snd_1914_);
lean_inc(v_fst_1913_);
lean_dec(v_a_1909_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1929_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1918_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1919_ = l_Lean_JsonNumber_fromNat(v_fst_1913_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 2);
lean_ctor_set(v___x_1911_, 0, v___x_1919_);
v___x_1921_ = v___x_1911_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_1921_);
lean_ctor_set(v___x_1916_, 0, v___x_1918_);
v___x_1923_ = v___x_1916_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_Json_mkObj(v___x_1925_);
lean_dec_ref_known(v___x_1925_, 2);
v_fst_1865_ = v___x_1926_;
v_snd_1866_ = v_snd_1914_;
goto v___jp_1864_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1848_, 1);
return v___x_1908_;
}
}
case 2:
{
lean_object* v_a_1931_; lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v_l_1848_, 0);
v_a_1932_ = lean_ctor_get(v_l_1848_, 1);
lean_inc(v_a_1931_);
v___x_1933_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1931_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1978_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1978_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1978_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_fst_1938_; lean_object* v_snd_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1977_; 
v_fst_1938_ = lean_ctor_get(v_a_1934_, 0);
v_snd_1939_ = lean_ctor_get(v_a_1934_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1934_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1941_ = v_a_1934_;
v_isShared_1942_ = v_isSharedCheck_1977_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_snd_1939_);
lean_inc(v_fst_1938_);
lean_dec(v_a_1934_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1977_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; 
lean_inc(v_a_1932_);
v___x_1943_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1932_, v_a_1849_, v_snd_1939_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1976_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1976_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1976_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1975_; 
v_fst_1948_ = lean_ctor_get(v_a_1944_, 0);
v_snd_1949_ = lean_ctor_get(v_a_1944_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_a_1944_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1951_ = v_a_1944_;
v_isShared_1952_ = v_isSharedCheck_1975_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_inc(v_fst_1948_);
lean_dec(v_a_1944_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1975_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1953_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1954_ = l_Lean_JsonNumber_fromNat(v_fst_1938_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 2);
lean_ctor_set(v___x_1946_, 0, v___x_1954_);
v___x_1956_ = v___x_1946_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = l_Lean_JsonNumber_fromNat(v_fst_1948_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 2);
lean_ctor_set(v___x_1936_, 0, v___x_1957_);
v___x_1959_ = v___x_1936_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1960_ = lean_unsigned_to_nat(2u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
v___x_1962_ = lean_array_push(v___x_1961_, v___x_1956_);
v___x_1963_ = lean_array_push(v___x_1962_, v___x_1959_);
v___x_1964_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___x_1964_);
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1966_ = v___x_1951_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_box(0);
if (v_isShared_1942_ == 0)
{
lean_ctor_set_tag(v___x_1941_, 1);
lean_ctor_set(v___x_1941_, 1, v___x_1967_);
lean_ctor_set(v___x_1941_, 0, v___x_1966_);
v___x_1969_ = v___x_1941_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_Json_mkObj(v___x_1969_);
lean_dec_ref(v___x_1969_);
v_fst_1865_ = v___x_1970_;
v_snd_1866_ = v_snd_1949_;
goto v___jp_1864_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1941_);
lean_dec(v_fst_1938_);
lean_del_object(v___x_1936_);
lean_dec_ref_known(v_l_1848_, 2);
return v___x_1943_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1848_, 2);
return v___x_1933_;
}
}
case 3:
{
lean_object* v_a_1979_; lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1979_ = lean_ctor_get(v_l_1848_, 0);
v_a_1980_ = lean_ctor_get(v_l_1848_, 1);
lean_inc(v_a_1979_);
v___x_1981_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1979_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2026_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2026_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2026_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2025_; 
v_fst_1986_ = lean_ctor_get(v_a_1982_, 0);
v_snd_1987_ = lean_ctor_get(v_a_1982_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1989_ = v_a_1982_;
v_isShared_1990_ = v_isSharedCheck_2025_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1987_);
lean_inc(v_fst_1986_);
lean_dec(v_a_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2025_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; 
lean_inc(v_a_1980_);
v___x_1991_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1980_, v_a_1849_, v_snd_1987_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2024_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2023_; 
v_fst_1996_ = lean_ctor_get(v_a_1992_, 0);
v_snd_1997_ = lean_ctor_get(v_a_1992_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1999_ = v_a_1992_;
v_isShared_2000_ = v_isSharedCheck_2023_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_snd_1997_);
lean_inc(v_fst_1996_);
lean_dec(v_a_1992_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2023_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2001_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_2002_ = l_Lean_JsonNumber_fromNat(v_fst_1986_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 2);
lean_ctor_set(v___x_1994_, 0, v___x_2002_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = l_Lean_JsonNumber_fromNat(v_fst_1996_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 2);
lean_ctor_set(v___x_1984_, 0, v___x_2005_);
v___x_2007_ = v___x_1984_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2008_ = lean_unsigned_to_nat(2u);
v___x_2009_ = lean_mk_empty_array_with_capacity(v___x_2008_);
v___x_2010_ = lean_array_push(v___x_2009_, v___x_2004_);
v___x_2011_ = lean_array_push(v___x_2010_, v___x_2007_);
v___x_2012_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 1, v___x_2012_);
lean_ctor_set(v___x_1999_, 0, v___x_2001_);
v___x_2014_ = v___x_1999_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 1);
lean_ctor_set(v___x_1989_, 1, v___x_2015_);
lean_ctor_set(v___x_1989_, 0, v___x_2014_);
v___x_2017_ = v___x_1989_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_Json_mkObj(v___x_2017_);
lean_dec_ref(v___x_2017_);
v_fst_1865_ = v___x_2018_;
v_snd_1866_ = v_snd_1997_;
goto v___jp_1864_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1989_);
lean_dec(v_fst_1986_);
lean_del_object(v___x_1984_);
lean_dec_ref_known(v_l_1848_, 2);
return v___x_1991_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1848_, 2);
return v___x_1981_;
}
}
case 4:
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v_l_1848_, 0);
lean_inc(v_a_2027_);
v___x_2028_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_2027_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2050_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2049_; 
v_fst_2033_ = lean_ctor_get(v_a_2029_, 0);
v_snd_2034_ = lean_ctor_get(v_a_2029_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2036_ = v_a_2029_;
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v_a_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_2039_ = l_Lean_JsonNumber_fromNat(v_fst_2033_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 2);
lean_ctor_set(v___x_2031_, 0, v___x_2039_);
v___x_2041_ = v___x_2031_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2041_);
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2043_ = v___x_2036_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = l_Lean_Json_mkObj(v___x_2045_);
lean_dec_ref_known(v___x_2045_, 2);
v_fst_1865_ = v___x_2046_;
v_snd_1866_ = v_snd_2034_;
goto v___jp_1864_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1848_, 1);
return v___x_2028_;
}
}
default: 
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_2052_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_2051_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v_fst_2054_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_fst_2054_);
v_snd_2055_ = lean_ctor_get(v_a_2053_, 1);
lean_inc(v_snd_2055_);
lean_dec(v_a_2053_);
v_fst_1865_ = v_fst_2054_;
v_snd_1866_ = v_snd_2055_;
goto v___jp_1864_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_l_1848_);
v_a_2056_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2052_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2052_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
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
v___jp_1864_:
{
lean_object* v_visitedLevels_1867_; lean_object* v_visitedNames_1868_; lean_object* v_visitedExprs_1869_; lean_object* v_visitedConstants_1870_; lean_object* v_noMDataExprs_1871_; uint8_t v_exportMData_1872_; uint8_t v_exportUnsafe_1873_; uint8_t v_ignoreMissing_1874_; lean_object* v_recursorMap_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1906_; 
v_visitedLevels_1867_ = lean_ctor_get(v_snd_1866_, 1);
v_visitedNames_1868_ = lean_ctor_get(v_snd_1866_, 0);
v_visitedExprs_1869_ = lean_ctor_get(v_snd_1866_, 2);
v_visitedConstants_1870_ = lean_ctor_get(v_snd_1866_, 3);
v_noMDataExprs_1871_ = lean_ctor_get(v_snd_1866_, 4);
v_exportMData_1872_ = lean_ctor_get_uint8(v_snd_1866_, sizeof(void*)*6);
v_exportUnsafe_1873_ = lean_ctor_get_uint8(v_snd_1866_, sizeof(void*)*6 + 1);
v_ignoreMissing_1874_ = lean_ctor_get_uint8(v_snd_1866_, sizeof(void*)*6 + 2);
v_recursorMap_1875_ = lean_ctor_get(v_snd_1866_, 5);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_snd_1866_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1877_ = v_snd_1866_;
v_isShared_1878_ = v_isSharedCheck_1906_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_recursorMap_1875_);
lean_inc(v_noMDataExprs_1871_);
lean_inc(v_visitedConstants_1870_);
lean_inc(v_visitedExprs_1869_);
lean_inc(v_visitedLevels_1867_);
lean_inc(v_visitedNames_1868_);
lean_dec(v_snd_1866_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1906_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_size_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_size_1879_ = lean_ctor_get(v_visitedLevels_1867_, 0);
lean_inc_n(v_size_1879_, 2);
v___x_1880_ = l_Lean_JsonNumber_fromNat(v_size_1879_);
v___x_1881_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
v___x_1882_ = l_Lean_Json_setObjVal_x21(v_fst_1865_, v___x_1863_, v___x_1881_);
v___x_1883_ = l_Lean_Json_compress(v___x_1882_);
v___x_1884_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1897_);
v___x_1886_ = v___x_1884_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_inc(v_size_1879_);
v___x_1888_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1867_, v_l_1848_, v_size_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1888_);
v___x_1890_ = v___x_1877_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_visitedNames_1868_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_visitedExprs_1869_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_visitedConstants_1870_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_noMDataExprs_1871_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_recursorMap_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*6, v_exportMData_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*6 + 1, v_exportUnsafe_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*6 + 2, v_ignoreMissing_1874_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_size_1879_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1891_);
v___x_1893_ = v___x_1886_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_size_1879_);
lean_del_object(v___x_1877_);
lean_dec(v_recursorMap_1875_);
lean_dec_ref(v_noMDataExprs_1871_);
lean_dec_ref(v_visitedConstants_1870_);
lean_dec_ref(v_visitedExprs_1869_);
lean_dec_ref(v_visitedNames_1868_);
lean_dec_ref(v_visitedLevels_1867_);
lean_dec(v_l_1848_);
v_a_1898_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1884_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1884_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_2064_, v_a_2065_, v_a_2066_);
lean_dec_ref(v_a_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_2069_, lean_object* v_m_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_2070_, v_a_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_2073_, lean_object* v_m_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_2073_, v_m_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_m_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_2077_, lean_object* v_a_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_2078_, v_x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2081_, lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_2081_, v_a_2082_, v_x_2083_);
lean_dec(v_x_2083_);
lean_dec(v_a_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
if (lean_obj_tag(v_a_2085_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l_List_reverse___redArg(v_a_2086_);
return v___x_2087_;
}
else
{
lean_object* v_head_2088_; lean_object* v_tail_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2098_; 
v_head_2088_ = lean_ctor_get(v_a_2085_, 0);
v_tail_2089_ = lean_ctor_get(v_a_2085_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2091_ = v_a_2085_;
v_isShared_2092_ = v_isSharedCheck_2098_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_tail_2089_);
lean_inc(v_head_2088_);
lean_dec(v_a_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2098_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = l_Lean_Level_param___override(v_head_2088_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_a_2086_);
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_a_2086_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v_a_2085_ = v_tail_2089_;
v_a_2086_ = v___x_2095_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_2099_, size_t v_i_2100_, lean_object* v_bs_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
if (v___x_2102_ == 0)
{
return v_bs_2101_;
}
else
{
lean_object* v_v_2103_; lean_object* v___x_2104_; lean_object* v_bs_x27_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v_v_2103_ = lean_array_uget(v_bs_2101_, v_i_2100_);
v___x_2104_ = lean_unsigned_to_nat(0u);
v_bs_x27_2105_ = lean_array_uset(v_bs_2101_, v_i_2100_, v___x_2104_);
v___x_2106_ = l_Lean_JsonNumber_fromNat(v_v_2103_);
v___x_2107_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2100_, v___x_2108_);
v___x_2110_ = lean_array_uset(v_bs_x27_2105_, v_i_2100_, v___x_2107_);
v_i_2100_ = v___x_2109_;
v_bs_2101_ = v___x_2110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_bs_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_2115_, v_i_boxed_2116_, v_bs_2114_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_2118_){
_start:
{
size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_sz_2119_ = lean_array_size(v_a_2118_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_2119_, v___x_2120_, v_a_2118_);
v___x_2122_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_array_mk(v_a_2123_);
v___x_2125_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
if (lean_obj_tag(v_x_2126_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = l_List_reverse___redArg(v_x_2127_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___y_2129_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
else
{
lean_object* v_head_2134_; lean_object* v_tail_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2155_; 
v_head_2134_ = lean_ctor_get(v_x_2126_, 0);
v_tail_2135_ = lean_ctor_get(v_x_2126_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_2126_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2137_ = v_x_2126_;
v_isShared_2138_ = v_isSharedCheck_2155_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_tail_2135_);
lean_inc(v_head_2134_);
lean_dec(v_x_2126_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2155_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_2134_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___x_2144_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v_fst_2141_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_fst_2141_);
v_snd_2142_ = lean_ctor_get(v_a_2140_, 1);
lean_inc(v_snd_2142_);
lean_dec(v_a_2140_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v_x_2127_);
lean_ctor_set(v___x_2137_, 0, v_fst_2141_);
v___x_2144_ = v___x_2137_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2141_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_x_2127_);
v___x_2144_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_x_2126_ = v_tail_2135_;
v_x_2127_ = v___x_2144_;
v___y_2129_ = v_snd_2142_;
goto _start;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_del_object(v___x_2137_);
lean_dec(v_tail_2135_);
lean_dec(v_x_2127_);
v_a_2147_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2139_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2139_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_2156_, v_x_2157_, v___y_2158_, v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = l_List_reverse___redArg(v_x_2163_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___y_2165_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2191_; 
v_head_2170_ = lean_ctor_get(v_x_2162_, 0);
v_tail_2171_ = lean_ctor_get(v_x_2162_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_x_2162_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2173_ = v_x_2162_;
v_isShared_2174_ = v_isSharedCheck_2191_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_tail_2171_);
lean_inc(v_head_2170_);
lean_dec(v_x_2162_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2191_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_2170_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v___x_2180_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v_fst_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_a_2176_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_a_2176_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_x_2163_);
lean_ctor_set(v___x_2173_, 0, v_fst_2177_);
v___x_2180_ = v___x_2173_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_fst_2177_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_x_2163_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
v_x_2162_ = v_tail_2171_;
v_x_2163_ = v___x_2180_;
v___y_2165_ = v_snd_2178_;
goto _start;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2173_);
lean_dec(v_tail_2171_);
lean_dec(v_x_2163_);
v_a_2183_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2175_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2175_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_2192_, v_x_2193_, v___y_2194_, v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_box(0);
lean_inc(v_uparams_2198_);
v___x_2203_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2198_, v___x_2202_, v_a_2199_, v_a_2200_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v_fst_2205_ = lean_ctor_get(v_a_2204_, 0);
lean_inc(v_fst_2205_);
v_snd_2206_ = lean_ctor_get(v_a_2204_, 1);
lean_inc(v_snd_2206_);
lean_dec(v_a_2204_);
v___x_2207_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_2198_, v___x_2202_);
v___x_2208_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_2207_, v___x_2202_, v_a_2199_, v_snd_2206_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2226_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2226_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2226_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2224_; 
v_snd_2213_ = lean_ctor_get(v_a_2209_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_a_2209_, 0);
lean_dec(v_unused_2225_);
v___x_2215_ = v_a_2209_;
v_isShared_2216_ = v_isSharedCheck_2224_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_dec(v_a_2209_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2224_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2205_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_snd_2213_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2219_);
v___x_2221_ = v___x_2211_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_fst_2205_);
v_a_2227_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2208_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2208_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_uparams_2198_);
v_a_2235_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2203_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2203_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2243_, v_a_2244_, v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2248_, v___x_2252_, v_a_2249_, v_a_2250_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2271_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2271_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2271_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2270_; 
v_fst_2258_ = lean_ctor_get(v_a_2254_, 0);
v_snd_2259_ = lean_ctor_get(v_a_2254_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2254_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2261_ = v_a_2254_;
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_snd_2259_);
lean_inc(v_fst_2258_);
lean_dec(v_a_2254_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2270_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2258_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_snd_2259_);
v___x_2265_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2267_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2265_);
v___x_2267_ = v___x_2256_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2253_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2253_);
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
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2280_, v_a_2281_, v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; lean_object* v___f_2290_; lean_object* v___f_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_11487__overap_2303_; lean_object* v___x_2304_; 
v___x_2289_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2290_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2290_, 0, v___x_2289_);
v___f_2291_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2291_, 0, v___x_2289_);
v___f_2292_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2292_, 0, v___x_2289_);
v___f_2293_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2293_, 0, v___x_2289_);
v___x_2294_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2294_, 0, lean_box(0));
lean_closure_set(v___x_2294_, 1, lean_box(0));
lean_closure_set(v___x_2294_, 2, v___x_2289_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___f_2290_);
v___x_2296_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2296_, 0, lean_box(0));
lean_closure_set(v___x_2296_, 1, lean_box(0));
lean_closure_set(v___x_2296_, 2, v___x_2289_);
v___x_2297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
lean_ctor_set(v___x_2297_, 2, v___f_2291_);
lean_ctor_set(v___x_2297_, 3, v___f_2292_);
lean_ctor_set(v___x_2297_, 4, v___f_2293_);
v___x_2298_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2298_, 0, lean_box(0));
lean_closure_set(v___x_2298_, 1, lean_box(0));
lean_closure_set(v___x_2298_, 2, v___x_2289_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_instInhabitedExpr;
v___x_2301_ = l_instInhabitedOfMonad___redArg(v___x_2299_, v___x_2300_);
v___f_2302_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2302_, 0, v___x_2301_);
v___x_11487__overap_2303_ = lean_panic_fn_borrowed(v___f_2302_, v_msg_2285_);
lean_dec_ref(v___f_2302_);
lean_inc_ref(v___y_2286_);
v___x_2304_ = lean_apply_3(v___x_11487__overap_2303_, v___y_2286_, v___y_2287_, lean_box(0));
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2305_, v___y_2306_, v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2310_, lean_object* v_b_2311_, lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2312_) == 0)
{
lean_dec(v_b_2311_);
lean_dec_ref(v_a_2310_);
return v_x_2312_;
}
else
{
lean_object* v_key_2313_; lean_object* v_value_2314_; lean_object* v_tail_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2327_; 
v_key_2313_ = lean_ctor_get(v_x_2312_, 0);
v_value_2314_ = lean_ctor_get(v_x_2312_, 1);
v_tail_2315_ = lean_ctor_get(v_x_2312_, 2);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_x_2312_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2317_ = v_x_2312_;
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_tail_2315_);
lean_inc(v_value_2314_);
lean_inc(v_key_2313_);
lean_dec(v_x_2312_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_expr_eqv(v_key_2313_, v_a_2310_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2310_, v_b_2311_, v_tail_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 2, v___x_2320_);
v___x_2322_ = v___x_2317_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_key_2313_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_value_2314_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v___x_2325_; 
lean_dec(v_value_2314_);
lean_dec(v_key_2313_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 1, v_b_2311_);
lean_ctor_set(v___x_2317_, 0, v_a_2310_);
v___x_2325_ = v___x_2317_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2310_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_b_2311_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_tail_2315_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2328_, lean_object* v_x_2329_){
_start:
{
if (lean_obj_tag(v_x_2329_) == 0)
{
return v_x_2328_;
}
else
{
lean_object* v_key_2330_; lean_object* v_value_2331_; lean_object* v_tail_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2355_; 
v_key_2330_ = lean_ctor_get(v_x_2329_, 0);
v_value_2331_ = lean_ctor_get(v_x_2329_, 1);
v_tail_2332_ = lean_ctor_get(v_x_2329_, 2);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_x_2329_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2334_ = v_x_2329_;
v_isShared_2335_ = v_isSharedCheck_2355_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_tail_2332_);
lean_inc(v_value_2331_);
lean_inc(v_key_2330_);
lean_dec(v_x_2329_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2355_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; uint64_t v___x_2337_; uint64_t v___x_2338_; uint64_t v___x_2339_; uint64_t v_fold_2340_; uint64_t v___x_2341_; uint64_t v___x_2342_; uint64_t v___x_2343_; size_t v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2336_ = lean_array_get_size(v_x_2328_);
v___x_2337_ = l_Lean_Expr_hash(v_key_2330_);
v___x_2338_ = 32ULL;
v___x_2339_ = lean_uint64_shift_right(v___x_2337_, v___x_2338_);
v_fold_2340_ = lean_uint64_xor(v___x_2337_, v___x_2339_);
v___x_2341_ = 16ULL;
v___x_2342_ = lean_uint64_shift_right(v_fold_2340_, v___x_2341_);
v___x_2343_ = lean_uint64_xor(v_fold_2340_, v___x_2342_);
v___x_2344_ = lean_uint64_to_usize(v___x_2343_);
v___x_2345_ = lean_usize_of_nat(v___x_2336_);
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_sub(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_usize_land(v___x_2344_, v___x_2347_);
v___x_2349_ = lean_array_uget_borrowed(v_x_2328_, v___x_2348_);
lean_inc(v___x_2349_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 2, v___x_2349_);
v___x_2351_ = v___x_2334_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_key_2330_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_value_2331_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_array_uset(v_x_2328_, v___x_2348_, v___x_2351_);
v_x_2328_ = v___x_2352_;
v_x_2329_ = v_tail_2332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2356_, lean_object* v_source_2357_, lean_object* v_target_2358_){
_start:
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_array_get_size(v_source_2357_);
v___x_2360_ = lean_nat_dec_lt(v_i_2356_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v_source_2357_);
lean_dec(v_i_2356_);
return v_target_2358_;
}
else
{
lean_object* v_es_2361_; lean_object* v___x_2362_; lean_object* v_source_2363_; lean_object* v_target_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_es_2361_ = lean_array_fget(v_source_2357_, v_i_2356_);
v___x_2362_ = lean_box(0);
v_source_2363_ = lean_array_fset(v_source_2357_, v_i_2356_, v___x_2362_);
v_target_2364_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2358_, v_es_2361_);
v___x_2365_ = lean_unsigned_to_nat(1u);
v___x_2366_ = lean_nat_add(v_i_2356_, v___x_2365_);
lean_dec(v_i_2356_);
v_i_2356_ = v___x_2366_;
v_source_2357_ = v_source_2363_;
v_target_2358_ = v_target_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2368_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_nbuckets_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2369_ = lean_array_get_size(v_data_2368_);
v___x_2370_ = lean_unsigned_to_nat(2u);
v_nbuckets_2371_ = lean_nat_mul(v___x_2369_, v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_mk_array(v_nbuckets_2371_, v___x_2373_);
v___x_2375_ = lean_array_propagate_mark(v_data_2368_, v___x_2374_);
v___x_2376_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2372_, v_data_2368_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
uint8_t v___x_2379_; 
v___x_2379_ = 0;
return v___x_2379_;
}
else
{
lean_object* v_key_2380_; lean_object* v_tail_2381_; uint8_t v___x_2382_; 
v_key_2380_ = lean_ctor_get(v_x_2378_, 0);
v_tail_2381_ = lean_ctor_get(v_x_2378_, 2);
v___x_2382_ = lean_expr_eqv(v_key_2380_, v_a_2377_);
if (v___x_2382_ == 0)
{
v_x_2378_ = v_tail_2381_;
goto _start;
}
else
{
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2384_, lean_object* v_x_2385_){
_start:
{
uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_res_2386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2384_, v_x_2385_);
lean_dec(v_x_2385_);
lean_dec_ref(v_a_2384_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2388_, lean_object* v_a_2389_, lean_object* v_b_2390_){
_start:
{
lean_object* v_size_2391_; lean_object* v_buckets_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2435_; 
v_size_2391_ = lean_ctor_get(v_m_2388_, 0);
v_buckets_2392_ = lean_ctor_get(v_m_2388_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_m_2388_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2394_ = v_m_2388_;
v_isShared_2395_ = v_isSharedCheck_2435_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_buckets_2392_);
lean_inc(v_size_2391_);
lean_dec(v_m_2388_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2435_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; uint64_t v___x_2397_; uint64_t v___x_2398_; uint64_t v___x_2399_; uint64_t v_fold_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; size_t v___x_2407_; size_t v___x_2408_; lean_object* v_bkt_2409_; uint8_t v___x_2410_; 
v___x_2396_ = lean_array_get_size(v_buckets_2392_);
v___x_2397_ = l_Lean_Expr_hash(v_a_2389_);
v___x_2398_ = 32ULL;
v___x_2399_ = lean_uint64_shift_right(v___x_2397_, v___x_2398_);
v_fold_2400_ = lean_uint64_xor(v___x_2397_, v___x_2399_);
v___x_2401_ = 16ULL;
v___x_2402_ = lean_uint64_shift_right(v_fold_2400_, v___x_2401_);
v___x_2403_ = lean_uint64_xor(v_fold_2400_, v___x_2402_);
v___x_2404_ = lean_uint64_to_usize(v___x_2403_);
v___x_2405_ = lean_usize_of_nat(v___x_2396_);
v___x_2406_ = ((size_t)1ULL);
v___x_2407_ = lean_usize_sub(v___x_2405_, v___x_2406_);
v___x_2408_ = lean_usize_land(v___x_2404_, v___x_2407_);
v_bkt_2409_ = lean_array_uget_borrowed(v_buckets_2392_, v___x_2408_);
v___x_2410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2389_, v_bkt_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v_size_x27_2412_; lean_object* v___x_2413_; lean_object* v_buckets_x27_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v_size_x27_2412_ = lean_nat_add(v_size_2391_, v___x_2411_);
lean_dec(v_size_2391_);
lean_inc(v_bkt_2409_);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v_a_2389_);
lean_ctor_set(v___x_2413_, 1, v_b_2390_);
lean_ctor_set(v___x_2413_, 2, v_bkt_2409_);
v_buckets_x27_2414_ = lean_array_uset(v_buckets_2392_, v___x_2408_, v___x_2413_);
v___x_2415_ = lean_unsigned_to_nat(4u);
v___x_2416_ = lean_nat_mul(v_size_x27_2412_, v___x_2415_);
v___x_2417_ = lean_unsigned_to_nat(3u);
v___x_2418_ = lean_nat_div(v___x_2416_, v___x_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_array_get_size(v_buckets_x27_2414_);
v___x_2420_ = lean_nat_dec_le(v___x_2418_, v___x_2419_);
lean_dec(v___x_2418_);
if (v___x_2420_ == 0)
{
lean_object* v_val_2421_; lean_object* v___x_2423_; 
v_val_2421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2414_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v_val_2421_);
lean_ctor_set(v___x_2394_, 0, v_size_x27_2412_);
v___x_2423_ = v___x_2394_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_size_x27_2412_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_val_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
else
{
lean_object* v___x_2426_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v_buckets_x27_2414_);
lean_ctor_set(v___x_2394_, 0, v_size_x27_2412_);
v___x_2426_ = v___x_2394_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_size_x27_2412_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_buckets_x27_2414_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v___x_2428_; lean_object* v_buckets_x27_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_inc(v_bkt_2409_);
v___x_2428_ = lean_box(0);
v_buckets_x27_2429_ = lean_array_uset(v_buckets_2392_, v___x_2408_, v___x_2428_);
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2389_, v_b_2390_, v_bkt_2409_);
v___x_2431_ = lean_array_uset(v_buckets_x27_2429_, v___x_2408_, v___x_2430_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2431_);
v___x_2433_ = v___x_2394_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_size_2391_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2436_, lean_object* v_x_2437_){
_start:
{
if (lean_obj_tag(v_x_2437_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_box(0);
return v___x_2438_;
}
else
{
lean_object* v_key_2439_; lean_object* v_value_2440_; lean_object* v_tail_2441_; uint8_t v___x_2442_; 
v_key_2439_ = lean_ctor_get(v_x_2437_, 0);
v_value_2440_ = lean_ctor_get(v_x_2437_, 1);
v_tail_2441_ = lean_ctor_get(v_x_2437_, 2);
v___x_2442_ = lean_expr_eqv(v_key_2439_, v_a_2436_);
if (v___x_2442_ == 0)
{
v_x_2437_ = v_tail_2441_;
goto _start;
}
else
{
lean_object* v___x_2444_; 
lean_inc(v_value_2440_);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_value_2440_);
return v___x_2444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2445_, v_x_2446_);
lean_dec(v_x_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_buckets_2450_; lean_object* v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; uint64_t v___x_2454_; uint64_t v_fold_2455_; uint64_t v___x_2456_; uint64_t v___x_2457_; uint64_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_buckets_2450_ = lean_ctor_get(v_m_2448_, 1);
v___x_2451_ = lean_array_get_size(v_buckets_2450_);
v___x_2452_ = l_Lean_Expr_hash(v_a_2449_);
v___x_2453_ = 32ULL;
v___x_2454_ = lean_uint64_shift_right(v___x_2452_, v___x_2453_);
v_fold_2455_ = lean_uint64_xor(v___x_2452_, v___x_2454_);
v___x_2456_ = 16ULL;
v___x_2457_ = lean_uint64_shift_right(v_fold_2455_, v___x_2456_);
v___x_2458_ = lean_uint64_xor(v_fold_2455_, v___x_2457_);
v___x_2459_ = lean_uint64_to_usize(v___x_2458_);
v___x_2460_ = lean_usize_of_nat(v___x_2451_);
v___x_2461_ = ((size_t)1ULL);
v___x_2462_ = lean_usize_sub(v___x_2460_, v___x_2461_);
v___x_2463_ = lean_usize_land(v___x_2459_, v___x_2462_);
v___x_2464_ = lean_array_uget_borrowed(v_buckets_2450_, v___x_2463_);
v___x_2465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2449_, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2466_, v_a_2467_);
lean_dec_ref(v_a_2467_);
lean_dec_ref(v_m_2466_);
return v_res_2468_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2470_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2471_ = lean_unsigned_to_nat(26u);
v___x_2472_ = lean_unsigned_to_nat(152u);
v___x_2473_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2474_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2475_ = l_mkPanicMessageWithDecl(v___x_2474_, v___x_2473_, v___x_2472_, v___x_2471_, v___x_2470_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_e_x27_2481_; lean_object* v_visitedNames_2482_; lean_object* v_visitedLevels_2483_; lean_object* v_visitedExprs_2484_; lean_object* v_visitedConstants_2485_; lean_object* v_noMDataExprs_2486_; uint8_t v_exportMData_2487_; uint8_t v_exportUnsafe_2488_; uint8_t v_ignoreMissing_2489_; lean_object* v_recursorMap_2490_; lean_object* v_e_x27_2496_; lean_object* v___y_2497_; lean_object* v_visitedNames_2507_; lean_object* v_visitedLevels_2508_; lean_object* v_visitedExprs_2509_; lean_object* v_visitedConstants_2510_; lean_object* v_noMDataExprs_2511_; uint8_t v_exportMData_2512_; uint8_t v_exportUnsafe_2513_; uint8_t v_ignoreMissing_2514_; lean_object* v_recursorMap_2515_; lean_object* v___x_2516_; 
v_visitedNames_2507_ = lean_ctor_get(v_a_2478_, 0);
v_visitedLevels_2508_ = lean_ctor_get(v_a_2478_, 1);
v_visitedExprs_2509_ = lean_ctor_get(v_a_2478_, 2);
v_visitedConstants_2510_ = lean_ctor_get(v_a_2478_, 3);
v_noMDataExprs_2511_ = lean_ctor_get(v_a_2478_, 4);
v_exportMData_2512_ = lean_ctor_get_uint8(v_a_2478_, sizeof(void*)*6);
v_exportUnsafe_2513_ = lean_ctor_get_uint8(v_a_2478_, sizeof(void*)*6 + 1);
v_ignoreMissing_2514_ = lean_ctor_get_uint8(v_a_2478_, sizeof(void*)*6 + 2);
v_recursorMap_2515_ = lean_ctor_get(v_a_2478_, 5);
v___x_2516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2511_, v_e_2476_);
if (lean_obj_tag(v___x_2516_) == 1)
{
lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_e_2476_);
v_val_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_val_2517_);
lean_ctor_set(v___x_2521_, 1, v_a_2478_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_dec(v___x_2516_);
switch(lean_obj_tag(v_e_2476_))
{
case 1:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2527_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2526_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v_fst_2529_; lean_object* v_snd_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v_fst_2529_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_fst_2529_);
v_snd_2530_ = lean_ctor_get(v_a_2528_, 1);
lean_inc(v_snd_2530_);
lean_dec(v_a_2528_);
v_e_x27_2496_ = v_fst_2529_;
v___y_2497_ = v_snd_2530_;
goto v___jp_2495_;
}
else
{
lean_dec_ref_known(v_e_2476_, 1);
return v___x_2527_;
}
}
case 2:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2532_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2531_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v_fst_2534_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v_a_2533_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_a_2533_);
v_e_x27_2496_ = v_fst_2534_;
v___y_2497_ = v_snd_2535_;
goto v___jp_2495_;
}
else
{
lean_dec_ref_known(v_e_2476_, 1);
return v___x_2532_;
}
}
case 5:
{
lean_object* v_fn_2536_; lean_object* v_arg_2537_; lean_object* v___x_2538_; 
v_fn_2536_ = lean_ctor_get(v_e_2476_, 0);
v_arg_2537_ = lean_ctor_get(v_e_2476_, 1);
lean_inc_ref(v_fn_2536_);
v___x_2538_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2536_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_fst_2540_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_fst_2540_);
v_snd_2541_ = lean_ctor_get(v_a_2539_, 1);
lean_inc(v_snd_2541_);
lean_dec(v_a_2539_);
lean_inc_ref(v_arg_2537_);
v___x_2542_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2537_, v_a_2477_, v_snd_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; size_t v___x_2546_; size_t v___x_2547_; uint8_t v___x_2548_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_fst_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2544_);
v_snd_2545_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_a_2543_);
v___x_2546_ = lean_ptr_addr(v_fn_2536_);
v___x_2547_ = lean_ptr_addr(v_fst_2540_);
v___x_2548_ = lean_usize_dec_eq(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Expr_app___override(v_fst_2540_, v_fst_2544_);
v_e_x27_2496_ = v___x_2549_;
v___y_2497_ = v_snd_2545_;
goto v___jp_2495_;
}
else
{
size_t v___x_2550_; size_t v___x_2551_; uint8_t v___x_2552_; 
v___x_2550_ = lean_ptr_addr(v_arg_2537_);
v___x_2551_ = lean_ptr_addr(v_fst_2544_);
v___x_2552_ = lean_usize_dec_eq(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Expr_app___override(v_fst_2540_, v_fst_2544_);
v_e_x27_2496_ = v___x_2553_;
v___y_2497_ = v_snd_2545_;
goto v___jp_2495_;
}
else
{
lean_dec(v_fst_2544_);
lean_dec(v_fst_2540_);
lean_inc_ref(v_e_2476_);
v_e_x27_2496_ = v_e_2476_;
v___y_2497_ = v_snd_2545_;
goto v___jp_2495_;
}
}
}
else
{
lean_dec(v_fst_2540_);
lean_dec_ref_known(v_e_2476_, 2);
return v___x_2542_;
}
}
else
{
lean_dec_ref_known(v_e_2476_, 2);
return v___x_2538_;
}
}
case 6:
{
lean_object* v_binderName_2554_; lean_object* v_binderType_2555_; lean_object* v_body_2556_; uint8_t v_binderInfo_2557_; lean_object* v___x_2558_; 
v_binderName_2554_ = lean_ctor_get(v_e_2476_, 0);
v_binderType_2555_ = lean_ctor_get(v_e_2476_, 1);
v_body_2556_ = lean_ctor_get(v_e_2476_, 2);
v_binderInfo_2557_ = lean_ctor_get_uint8(v_e_2476_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2555_);
v___x_2558_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2555_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v_fst_2560_; lean_object* v_snd_2561_; lean_object* v___x_2562_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v_fst_2560_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_fst_2560_);
v_snd_2561_ = lean_ctor_get(v_a_2559_, 1);
lean_inc(v_snd_2561_);
lean_dec(v_a_2559_);
lean_inc_ref(v_body_2556_);
v___x_2562_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2556_, v_a_2477_, v_snd_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; size_t v___x_2566_; size_t v___x_2567_; uint8_t v___x_2568_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v_fst_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_fst_2564_);
v_snd_2565_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_snd_2565_);
lean_dec(v_a_2563_);
v___x_2566_ = lean_ptr_addr(v_binderType_2555_);
v___x_2567_ = lean_ptr_addr(v_fst_2560_);
v___x_2568_ = lean_usize_dec_eq(v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_inc(v_binderName_2554_);
v___x_2569_ = l_Lean_Expr_lam___override(v_binderName_2554_, v_fst_2560_, v_fst_2564_, v_binderInfo_2557_);
v_e_x27_2496_ = v___x_2569_;
v___y_2497_ = v_snd_2565_;
goto v___jp_2495_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_ptr_addr(v_body_2556_);
v___x_2571_ = lean_ptr_addr(v_fst_2564_);
v___x_2572_ = lean_usize_dec_eq(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_inc(v_binderName_2554_);
v___x_2573_ = l_Lean_Expr_lam___override(v_binderName_2554_, v_fst_2560_, v_fst_2564_, v_binderInfo_2557_);
v_e_x27_2496_ = v___x_2573_;
v___y_2497_ = v_snd_2565_;
goto v___jp_2495_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2557_, v_binderInfo_2557_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_inc(v_binderName_2554_);
v___x_2575_ = l_Lean_Expr_lam___override(v_binderName_2554_, v_fst_2560_, v_fst_2564_, v_binderInfo_2557_);
v_e_x27_2496_ = v___x_2575_;
v___y_2497_ = v_snd_2565_;
goto v___jp_2495_;
}
else
{
lean_dec(v_fst_2564_);
lean_dec(v_fst_2560_);
lean_inc_ref(v_e_2476_);
v_e_x27_2496_ = v_e_2476_;
v___y_2497_ = v_snd_2565_;
goto v___jp_2495_;
}
}
}
}
else
{
lean_dec(v_fst_2560_);
lean_dec_ref_known(v_e_2476_, 3);
return v___x_2562_;
}
}
else
{
lean_dec_ref_known(v_e_2476_, 3);
return v___x_2558_;
}
}
case 7:
{
lean_object* v_binderName_2576_; lean_object* v_binderType_2577_; lean_object* v_body_2578_; uint8_t v_binderInfo_2579_; lean_object* v___x_2580_; 
v_binderName_2576_ = lean_ctor_get(v_e_2476_, 0);
v_binderType_2577_ = lean_ctor_get(v_e_2476_, 1);
v_body_2578_ = lean_ctor_get(v_e_2476_, 2);
v_binderInfo_2579_ = lean_ctor_get_uint8(v_e_2476_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2577_);
v___x_2580_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2577_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v_fst_2582_; lean_object* v_snd_2583_; lean_object* v___x_2584_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v_fst_2582_ = lean_ctor_get(v_a_2581_, 0);
lean_inc(v_fst_2582_);
v_snd_2583_ = lean_ctor_get(v_a_2581_, 1);
lean_inc(v_snd_2583_);
lean_dec(v_a_2581_);
lean_inc_ref(v_body_2578_);
v___x_2584_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2578_, v_a_2477_, v_snd_2583_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; size_t v___x_2588_; size_t v___x_2589_; uint8_t v___x_2590_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_fst_2586_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_fst_2586_);
v_snd_2587_ = lean_ctor_get(v_a_2585_, 1);
lean_inc(v_snd_2587_);
lean_dec(v_a_2585_);
v___x_2588_ = lean_ptr_addr(v_binderType_2577_);
v___x_2589_ = lean_ptr_addr(v_fst_2582_);
v___x_2590_ = lean_usize_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_inc(v_binderName_2576_);
v___x_2591_ = l_Lean_Expr_forallE___override(v_binderName_2576_, v_fst_2582_, v_fst_2586_, v_binderInfo_2579_);
v_e_x27_2496_ = v___x_2591_;
v___y_2497_ = v_snd_2587_;
goto v___jp_2495_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = lean_ptr_addr(v_body_2578_);
v___x_2593_ = lean_ptr_addr(v_fst_2586_);
v___x_2594_ = lean_usize_dec_eq(v___x_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_inc(v_binderName_2576_);
v___x_2595_ = l_Lean_Expr_forallE___override(v_binderName_2576_, v_fst_2582_, v_fst_2586_, v_binderInfo_2579_);
v_e_x27_2496_ = v___x_2595_;
v___y_2497_ = v_snd_2587_;
goto v___jp_2495_;
}
else
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2579_, v_binderInfo_2579_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
lean_inc(v_binderName_2576_);
v___x_2597_ = l_Lean_Expr_forallE___override(v_binderName_2576_, v_fst_2582_, v_fst_2586_, v_binderInfo_2579_);
v_e_x27_2496_ = v___x_2597_;
v___y_2497_ = v_snd_2587_;
goto v___jp_2495_;
}
else
{
lean_dec(v_fst_2586_);
lean_dec(v_fst_2582_);
lean_inc_ref(v_e_2476_);
v_e_x27_2496_ = v_e_2476_;
v___y_2497_ = v_snd_2587_;
goto v___jp_2495_;
}
}
}
}
else
{
lean_dec(v_fst_2582_);
lean_dec_ref_known(v_e_2476_, 3);
return v___x_2584_;
}
}
else
{
lean_dec_ref_known(v_e_2476_, 3);
return v___x_2580_;
}
}
case 8:
{
lean_object* v_declName_2598_; lean_object* v_type_2599_; lean_object* v_value_2600_; lean_object* v_body_2601_; uint8_t v_nondep_2602_; lean_object* v___x_2603_; 
v_declName_2598_ = lean_ctor_get(v_e_2476_, 0);
v_type_2599_ = lean_ctor_get(v_e_2476_, 1);
v_value_2600_ = lean_ctor_get(v_e_2476_, 2);
v_body_2601_ = lean_ctor_get(v_e_2476_, 3);
v_nondep_2602_ = lean_ctor_get_uint8(v_e_2476_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2599_);
v___x_2603_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2599_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v_fst_2605_; lean_object* v_snd_2606_; lean_object* v___x_2607_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v_fst_2605_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_fst_2605_);
v_snd_2606_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_a_2604_);
lean_inc_ref(v_value_2600_);
v___x_2607_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2600_, v_a_2477_, v_snd_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v_fst_2609_; lean_object* v_snd_2610_; lean_object* v___x_2611_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v_fst_2609_ = lean_ctor_get(v_a_2608_, 0);
lean_inc(v_fst_2609_);
v_snd_2610_ = lean_ctor_get(v_a_2608_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_a_2608_);
lean_inc_ref(v_body_2601_);
v___x_2611_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2601_, v_a_2477_, v_snd_2610_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; uint8_t v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; uint8_t v___x_2618_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_fst_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_fst_2613_);
v_snd_2614_ = lean_ctor_get(v_a_2612_, 1);
lean_inc(v_snd_2614_);
lean_dec(v_a_2612_);
v___x_2615_ = 0;
v___x_2616_ = lean_ptr_addr(v_type_2599_);
v___x_2617_ = lean_ptr_addr(v_fst_2605_);
v___x_2618_ = lean_usize_dec_eq(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_inc(v_declName_2598_);
v___x_2619_ = l_Lean_Expr_letE___override(v_declName_2598_, v_fst_2605_, v_fst_2609_, v_fst_2613_, v___x_2615_);
v_e_x27_2496_ = v___x_2619_;
v___y_2497_ = v_snd_2614_;
goto v___jp_2495_;
}
else
{
size_t v___x_2620_; size_t v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = lean_ptr_addr(v_value_2600_);
v___x_2621_ = lean_ptr_addr(v_fst_2609_);
v___x_2622_ = lean_usize_dec_eq(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_inc(v_declName_2598_);
v___x_2623_ = l_Lean_Expr_letE___override(v_declName_2598_, v_fst_2605_, v_fst_2609_, v_fst_2613_, v___x_2615_);
v_e_x27_2496_ = v___x_2623_;
v___y_2497_ = v_snd_2614_;
goto v___jp_2495_;
}
else
{
size_t v___x_2624_; size_t v___x_2625_; uint8_t v___x_2626_; 
v___x_2624_ = lean_ptr_addr(v_body_2601_);
v___x_2625_ = lean_ptr_addr(v_fst_2613_);
v___x_2626_ = lean_usize_dec_eq(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_inc(v_declName_2598_);
v___x_2627_ = l_Lean_Expr_letE___override(v_declName_2598_, v_fst_2605_, v_fst_2609_, v_fst_2613_, v___x_2615_);
v_e_x27_2496_ = v___x_2627_;
v___y_2497_ = v_snd_2614_;
goto v___jp_2495_;
}
else
{
if (v_nondep_2602_ == 0)
{
lean_dec(v_fst_2613_);
lean_dec(v_fst_2609_);
lean_dec(v_fst_2605_);
lean_inc_ref(v_e_2476_);
v_e_x27_2496_ = v_e_2476_;
v___y_2497_ = v_snd_2614_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2628_; 
lean_inc(v_declName_2598_);
v___x_2628_ = l_Lean_Expr_letE___override(v_declName_2598_, v_fst_2605_, v_fst_2609_, v_fst_2613_, v___x_2615_);
v_e_x27_2496_ = v___x_2628_;
v___y_2497_ = v_snd_2614_;
goto v___jp_2495_;
}
}
}
}
}
else
{
lean_dec(v_fst_2609_);
lean_dec(v_fst_2605_);
lean_dec_ref_known(v_e_2476_, 4);
return v___x_2611_;
}
}
else
{
lean_dec(v_fst_2605_);
lean_dec_ref_known(v_e_2476_, 4);
return v___x_2607_;
}
}
else
{
lean_dec_ref_known(v_e_2476_, 4);
return v___x_2603_;
}
}
case 10:
{
lean_object* v_expr_2629_; lean_object* v___x_2630_; 
v_expr_2629_ = lean_ctor_get(v_e_2476_, 1);
lean_inc_ref(v_expr_2629_);
v___x_2630_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2629_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v_fst_2632_; lean_object* v_snd_2633_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v_fst_2632_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_fst_2632_);
v_snd_2633_ = lean_ctor_get(v_a_2631_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2631_);
v_e_x27_2496_ = v_fst_2632_;
v___y_2497_ = v_snd_2633_;
goto v___jp_2495_;
}
else
{
lean_dec_ref_known(v_e_2476_, 2);
return v___x_2630_;
}
}
case 11:
{
lean_object* v_typeName_2634_; lean_object* v_idx_2635_; lean_object* v_struct_2636_; lean_object* v___x_2637_; 
v_typeName_2634_ = lean_ctor_get(v_e_2476_, 0);
v_idx_2635_ = lean_ctor_get(v_e_2476_, 1);
v_struct_2636_ = lean_ctor_get(v_e_2476_, 2);
lean_inc_ref(v_struct_2636_);
v___x_2637_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2636_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v_fst_2639_; lean_object* v_snd_2640_; size_t v___x_2641_; size_t v___x_2642_; uint8_t v___x_2643_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v_fst_2639_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_fst_2639_);
v_snd_2640_ = lean_ctor_get(v_a_2638_, 1);
lean_inc(v_snd_2640_);
lean_dec(v_a_2638_);
v___x_2641_ = lean_ptr_addr(v_struct_2636_);
v___x_2642_ = lean_ptr_addr(v_fst_2639_);
v___x_2643_ = lean_usize_dec_eq(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_inc(v_idx_2635_);
lean_inc(v_typeName_2634_);
v___x_2644_ = l_Lean_Expr_proj___override(v_typeName_2634_, v_idx_2635_, v_fst_2639_);
v_e_x27_2496_ = v___x_2644_;
v___y_2497_ = v_snd_2640_;
goto v___jp_2495_;
}
else
{
lean_dec(v_fst_2639_);
lean_inc_ref(v_e_2476_);
v_e_x27_2496_ = v_e_2476_;
v___y_2497_ = v_snd_2640_;
goto v___jp_2495_;
}
}
else
{
lean_dec_ref_known(v_e_2476_, 3);
return v___x_2637_;
}
}
default: 
{
lean_inc(v_recursorMap_2515_);
lean_inc_ref(v_noMDataExprs_2511_);
lean_inc_ref(v_visitedConstants_2510_);
lean_inc_ref(v_visitedExprs_2509_);
lean_inc_ref(v_visitedLevels_2508_);
lean_inc_ref(v_visitedNames_2507_);
lean_dec_ref(v_a_2478_);
lean_inc_ref(v_e_2476_);
v_e_x27_2481_ = v_e_2476_;
v_visitedNames_2482_ = v_visitedNames_2507_;
v_visitedLevels_2483_ = v_visitedLevels_2508_;
v_visitedExprs_2484_ = v_visitedExprs_2509_;
v_visitedConstants_2485_ = v_visitedConstants_2510_;
v_noMDataExprs_2486_ = v_noMDataExprs_2511_;
v_exportMData_2487_ = v_exportMData_2512_;
v_exportUnsafe_2488_ = v_exportUnsafe_2513_;
v_ignoreMissing_2489_ = v_ignoreMissing_2514_;
v_recursorMap_2490_ = v_recursorMap_2515_;
goto v___jp_2480_;
}
}
}
v___jp_2480_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_inc_ref(v_e_x27_2481_);
v___x_2491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2486_, v_e_2476_, v_e_x27_2481_);
v___x_2492_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2492_, 0, v_visitedNames_2482_);
lean_ctor_set(v___x_2492_, 1, v_visitedLevels_2483_);
lean_ctor_set(v___x_2492_, 2, v_visitedExprs_2484_);
lean_ctor_set(v___x_2492_, 3, v_visitedConstants_2485_);
lean_ctor_set(v___x_2492_, 4, v___x_2491_);
lean_ctor_set(v___x_2492_, 5, v_recursorMap_2490_);
lean_ctor_set_uint8(v___x_2492_, sizeof(void*)*6, v_exportMData_2487_);
lean_ctor_set_uint8(v___x_2492_, sizeof(void*)*6 + 1, v_exportUnsafe_2488_);
lean_ctor_set_uint8(v___x_2492_, sizeof(void*)*6 + 2, v_ignoreMissing_2489_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_e_x27_2481_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
v___jp_2495_:
{
lean_object* v_visitedNames_2498_; lean_object* v_visitedLevels_2499_; lean_object* v_visitedExprs_2500_; lean_object* v_visitedConstants_2501_; lean_object* v_noMDataExprs_2502_; uint8_t v_exportMData_2503_; uint8_t v_exportUnsafe_2504_; uint8_t v_ignoreMissing_2505_; lean_object* v_recursorMap_2506_; 
v_visitedNames_2498_ = lean_ctor_get(v___y_2497_, 0);
lean_inc_ref(v_visitedNames_2498_);
v_visitedLevels_2499_ = lean_ctor_get(v___y_2497_, 1);
lean_inc_ref(v_visitedLevels_2499_);
v_visitedExprs_2500_ = lean_ctor_get(v___y_2497_, 2);
lean_inc_ref(v_visitedExprs_2500_);
v_visitedConstants_2501_ = lean_ctor_get(v___y_2497_, 3);
lean_inc_ref(v_visitedConstants_2501_);
v_noMDataExprs_2502_ = lean_ctor_get(v___y_2497_, 4);
lean_inc_ref(v_noMDataExprs_2502_);
v_exportMData_2503_ = lean_ctor_get_uint8(v___y_2497_, sizeof(void*)*6);
v_exportUnsafe_2504_ = lean_ctor_get_uint8(v___y_2497_, sizeof(void*)*6 + 1);
v_ignoreMissing_2505_ = lean_ctor_get_uint8(v___y_2497_, sizeof(void*)*6 + 2);
v_recursorMap_2506_ = lean_ctor_get(v___y_2497_, 5);
lean_inc(v_recursorMap_2506_);
lean_dec_ref(v___y_2497_);
v_e_x27_2481_ = v_e_x27_2496_;
v_visitedNames_2482_ = v_visitedNames_2498_;
v_visitedLevels_2483_ = v_visitedLevels_2499_;
v_visitedExprs_2484_ = v_visitedExprs_2500_;
v_visitedConstants_2485_ = v_visitedConstants_2501_;
v_noMDataExprs_2486_ = v_noMDataExprs_2502_;
v_exportMData_2487_ = v_exportMData_2503_;
v_exportUnsafe_2488_ = v_exportUnsafe_2504_;
v_ignoreMissing_2489_ = v_ignoreMissing_2505_;
v_recursorMap_2490_ = v_recursorMap_2506_;
goto v___jp_2480_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2645_, v_a_2646_, v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2650_, lean_object* v_m_2651_, lean_object* v_a_2652_, lean_object* v_b_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2651_, v_a_2652_, v_b_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2655_, lean_object* v_m_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2656_, v_a_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2659_, lean_object* v_m_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2659_, v_m_2660_, v_a_2661_);
lean_dec_ref(v_a_2661_);
lean_dec_ref(v_m_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2663_, lean_object* v_a_2664_, lean_object* v_x_2665_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_a_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2667_, v_a_2668_, v_x_2669_);
lean_dec(v_x_2669_);
lean_dec_ref(v_a_2668_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2672_, lean_object* v_data_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2675_, lean_object* v_a_2676_, lean_object* v_b_2677_, lean_object* v_x_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2676_, v_b_2677_, v_x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2680_, lean_object* v_a_2681_, lean_object* v_x_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2681_, v_x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2684_, lean_object* v_a_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2684_, v_a_2685_, v_x_2686_);
lean_dec(v_x_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2688_, lean_object* v_i_2689_, lean_object* v_source_2690_, lean_object* v_target_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2689_, v_source_2690_, v_target_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2694_, v_x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = l_Lean_Json_mkObj(v_fields_2697_);
v___x_2701_ = l_Lean_Json_compress(v___x_2700_);
v___x_2702_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2701_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2711_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_a_2703_);
lean_ctor_set(v___x_2707_, 1, v_a_2698_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2707_);
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v_a_2698_);
v_a_2712_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2702_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2702_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2720_, v_a_2721_);
lean_dec(v_fields_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2724_, v_a_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2729_, v_a_2730_, v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_fields_2729_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2734_, lean_object* v_k_2735_){
_start:
{
if (lean_obj_tag(v_t_2734_) == 0)
{
lean_object* v_k_2736_; lean_object* v_v_2737_; lean_object* v_l_2738_; lean_object* v_r_2739_; uint8_t v___x_2740_; 
v_k_2736_ = lean_ctor_get(v_t_2734_, 1);
v_v_2737_ = lean_ctor_get(v_t_2734_, 2);
v_l_2738_ = lean_ctor_get(v_t_2734_, 3);
v_r_2739_ = lean_ctor_get(v_t_2734_, 4);
v___x_2740_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2735_, v_k_2736_);
switch(v___x_2740_)
{
case 0:
{
v_t_2734_ = v_l_2738_;
goto _start;
}
case 1:
{
lean_object* v___x_2742_; 
lean_inc(v_v_2737_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_v_2737_);
return v___x_2742_;
}
default: 
{
v_t_2734_ = v_r_2739_;
goto _start;
}
}
}
else
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2745_, lean_object* v_k_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2745_, v_k_2746_);
lean_dec(v_k_2746_);
lean_dec(v_t_2745_);
return v_res_2747_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Array_instInhabited___redArg();
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___f_2767_; lean_object* v___x_163499__overap_2768_; lean_object* v___x_2769_; 
v___x_2753_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2754_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2754_, 0, v___x_2753_);
v___f_2755_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2755_, 0, v___x_2753_);
v___f_2756_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2756_, 0, v___x_2753_);
v___f_2757_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2757_, 0, v___x_2753_);
v___x_2758_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2758_, 0, lean_box(0));
lean_closure_set(v___x_2758_, 1, lean_box(0));
lean_closure_set(v___x_2758_, 2, v___x_2753_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___f_2754_);
v___x_2760_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2760_, 0, lean_box(0));
lean_closure_set(v___x_2760_, 1, lean_box(0));
lean_closure_set(v___x_2760_, 2, v___x_2753_);
v___x_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
lean_ctor_set(v___x_2761_, 2, v___f_2755_);
lean_ctor_set(v___x_2761_, 3, v___f_2756_);
lean_ctor_set(v___x_2761_, 4, v___f_2757_);
v___x_2762_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2762_, 0, lean_box(0));
lean_closure_set(v___x_2762_, 1, lean_box(0));
lean_closure_set(v___x_2762_, 2, v___x_2753_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
v___x_2766_ = l_instInhabitedOfMonad___redArg(v___x_2763_, v___x_2765_);
v___f_2767_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2767_, 0, v___x_2766_);
v___x_163499__overap_2768_ = lean_panic_fn_borrowed(v___f_2767_, v_msg_2749_);
lean_dec_ref(v___f_2767_);
lean_inc_ref(v___y_2750_);
v___x_2769_ = lean_apply_3(v___x_163499__overap_2768_, v___y_2750_, v___y_2751_, lean_box(0));
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2770_, v___y_2771_, v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___f_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___f_2792_; lean_object* v___x_162777__overap_2793_; lean_object* v___x_2794_; 
v___x_2779_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2780_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2780_, 0, v___x_2779_);
v___f_2781_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2781_, 0, v___x_2779_);
v___f_2782_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2782_, 0, v___x_2779_);
v___f_2783_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2783_, 0, v___x_2779_);
v___x_2784_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2784_, 0, lean_box(0));
lean_closure_set(v___x_2784_, 1, lean_box(0));
lean_closure_set(v___x_2784_, 2, v___x_2779_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___f_2780_);
v___x_2786_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2786_, 0, lean_box(0));
lean_closure_set(v___x_2786_, 1, lean_box(0));
lean_closure_set(v___x_2786_, 2, v___x_2779_);
v___x_2787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
lean_ctor_set(v___x_2787_, 2, v___f_2781_);
lean_ctor_set(v___x_2787_, 3, v___f_2782_);
lean_ctor_set(v___x_2787_, 4, v___f_2783_);
v___x_2788_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2788_, 0, lean_box(0));
lean_closure_set(v___x_2788_, 1, lean_box(0));
lean_closure_set(v___x_2788_, 2, v___x_2779_);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_instInhabitedOfMonad___redArg(v___x_2789_, v___x_2790_);
v___f_2792_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2792_, 0, v___x_2791_);
v___x_162777__overap_2793_ = lean_panic_fn_borrowed(v___f_2792_, v_msg_2775_);
lean_dec_ref(v___f_2792_);
lean_inc_ref(v___y_2776_);
v___x_2794_ = lean_apply_3(v___x_162777__overap_2793_, v___y_2776_, v___y_2777_, lean_box(0));
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2795_, v___y_2796_, v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2800_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2802_ = lean_panic_fn_borrowed(v___x_2801_, v_msg_2800_);
return v___x_2802_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2805_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1));
v___x_2806_ = lean_unsigned_to_nat(10u);
v___x_2807_ = lean_unsigned_to_nat(334u);
v___x_2808_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2809_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2810_ = l_mkPanicMessageWithDecl(v___x_2809_, v___x_2808_, v___x_2807_, v___x_2806_, v___x_2805_);
return v___x_2810_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2812_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3));
v___x_2813_ = lean_unsigned_to_nat(15u);
v___x_2814_ = lean_unsigned_to_nat(336u);
v___x_2815_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2816_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2817_ = l_mkPanicMessageWithDecl(v___x_2816_, v___x_2815_, v___x_2814_, v___x_2813_, v___x_2812_);
return v___x_2817_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2821_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7));
v___x_2822_ = lean_unsigned_to_nat(14u);
v___x_2823_ = lean_unsigned_to_nat(22u);
v___x_2824_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6));
v___x_2825_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5));
v___x_2826_ = l_mkPanicMessageWithDecl(v___x_2825_, v___x_2824_, v___x_2823_, v___x_2822_, v___x_2821_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2827_, uint8_t v___x_2828_, lean_object* v_as_x27_2829_, lean_object* v_b_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
if (lean_obj_tag(v_as_x27_2829_) == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_b_2830_);
lean_ctor_set(v___x_2834_, 1, v___y_2832_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
else
{
lean_object* v_head_2836_; lean_object* v_tail_2837_; lean_object* v___y_2839_; lean_object* v___y_2843_; lean_object* v___y_2878_; lean_object* v___x_2894_; 
v_head_2836_ = lean_ctor_get(v_as_x27_2829_, 0);
v_tail_2837_ = lean_ctor_get(v_as_x27_2829_, 1);
lean_inc(v_head_2836_);
lean_inc_ref(v___y_2831_);
v___x_2894_ = l_Lean_Environment_find_x3f(v___y_2831_, v_head_2836_, v___x_2828_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2896_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2895_);
v___y_2878_ = v___x_2896_;
goto v___jp_2877_;
}
else
{
lean_object* v_val_2897_; 
v_val_2897_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v___x_2894_, 1);
v___y_2878_ = v_val_2897_;
goto v___jp_2877_;
}
v___jp_2838_:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_array_push(v_b_2830_, v___y_2839_);
v_as_x27_2829_ = v_tail_2837_;
v_b_2830_ = v___x_2840_;
goto _start;
}
v___jp_2842_:
{
uint8_t v_exportUnsafe_2844_; 
v_exportUnsafe_2844_ = lean_ctor_get_uint8(v___y_2832_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_b_2830_);
v___x_2845_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2);
v___x_2846_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2845_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2868_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_fst_2851_; 
v_fst_2851_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_fst_2851_);
if (lean_obj_tag(v_fst_2851_) == 0)
{
lean_object* v_snd_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2863_; 
v_snd_2852_ = lean_ctor_get(v_a_2847_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v_a_2847_, 0);
lean_dec(v_unused_2864_);
v___x_2854_ = v_a_2847_;
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_snd_2852_);
lean_dec(v_a_2847_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v_a_2856_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v_fst_2851_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v_fst_2851_, 1);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v_a_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_snd_2852_);
v___x_2858_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2860_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2858_);
v___x_2860_ = v___x_2849_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_snd_2865_; lean_object* v_a_2866_; 
lean_del_object(v___x_2849_);
v_snd_2865_ = lean_ctor_get(v_a_2847_, 1);
lean_inc(v_snd_2865_);
lean_dec(v_a_2847_);
v_a_2866_ = lean_ctor_get(v_fst_2851_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v_fst_2851_, 1);
v_as_x27_2829_ = v_tail_2837_;
v_b_2830_ = v_a_2866_;
v___y_2832_ = v_snd_2865_;
goto _start;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2846_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2846_);
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
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
v___y_2839_ = v___y_2843_;
goto v___jp_2838_;
}
}
v___jp_2877_:
{
if (lean_obj_tag(v___y_2878_) == 6)
{
lean_object* v_val_2879_; uint8_t v_isUnsafe_2880_; 
v_val_2879_ = lean_ctor_get(v___y_2878_, 0);
lean_inc_ref(v_val_2879_);
lean_dec_ref_known(v___y_2878_, 1);
v_isUnsafe_2880_ = lean_ctor_get_uint8(v_val_2879_, sizeof(void*)*5);
if (v_isUnsafe_2880_ == 0)
{
if (v___y_2827_ == 0)
{
v___y_2843_ = v_val_2879_;
goto v___jp_2842_;
}
else
{
v___y_2839_ = v_val_2879_;
goto v___jp_2838_;
}
}
else
{
v___y_2843_ = v_val_2879_;
goto v___jp_2842_;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v___y_2878_);
v___x_2881_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4);
v___x_2882_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2881_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_snd_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_snd_2884_ = lean_ctor_get(v_a_2883_, 1);
lean_inc(v_snd_2884_);
lean_dec(v_a_2883_);
v_as_x27_2829_ = v_tail_2837_;
v___y_2832_ = v_snd_2884_;
goto _start;
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v_b_2830_);
v_a_2886_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2882_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2882_);
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
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2898_, lean_object* v___x_2899_, lean_object* v_as_x27_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v___y_172148__boxed_2905_; uint8_t v___x_172149__boxed_2906_; lean_object* v_res_2907_; 
v___y_172148__boxed_2905_ = lean_unbox(v___y_2898_);
v___x_172149__boxed_2906_ = lean_unbox(v___x_2899_);
v_res_2907_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172148__boxed_2905_, v___x_172149__boxed_2906_, v_as_x27_2900_, v_b_2901_, v___y_2902_, v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v_as_x27_2900_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; lean_object* v___f_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___x_164180__overap_2930_; lean_object* v___x_2931_; 
v___x_2912_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2913_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2913_, 0, v___x_2912_);
v___f_2914_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2914_, 0, v___x_2912_);
v___f_2915_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2915_, 0, v___x_2912_);
v___f_2916_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2916_, 0, v___x_2912_);
v___x_2917_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2917_, 0, lean_box(0));
lean_closure_set(v___x_2917_, 1, lean_box(0));
lean_closure_set(v___x_2917_, 2, v___x_2912_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v___f_2913_);
v___x_2919_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2919_, 0, lean_box(0));
lean_closure_set(v___x_2919_, 1, lean_box(0));
lean_closure_set(v___x_2919_, 2, v___x_2912_);
v___x_2920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
lean_ctor_set(v___x_2920_, 2, v___f_2914_);
lean_ctor_set(v___x_2920_, 3, v___f_2915_);
lean_ctor_set(v___x_2920_, 4, v___f_2916_);
v___x_2921_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2921_, 0, lean_box(0));
lean_closure_set(v___x_2921_, 1, lean_box(0));
lean_closure_set(v___x_2921_, 2, v___x_2912_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2924_ = lean_box(1);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2923_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = l_instInhabitedOfMonad___redArg(v___x_2922_, v___x_2927_);
v___f_2929_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2929_, 0, v___x_2928_);
v___x_164180__overap_2930_ = lean_panic_fn_borrowed(v___f_2929_, v_msg_2908_);
lean_dec_ref(v___f_2929_);
lean_inc_ref(v___y_2909_);
v___x_2931_ = lean_apply_3(v___x_164180__overap_2930_, v___y_2909_, v___y_2910_, lean_box(0));
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; lean_object* v___x_162765__overap_2956_; lean_object* v___x_2957_; 
v___x_2941_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2942_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2942_, 0, v___x_2941_);
v___f_2943_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2943_, 0, v___x_2941_);
v___f_2944_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2944_, 0, v___x_2941_);
v___f_2945_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2945_, 0, v___x_2941_);
v___x_2946_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2946_, 0, lean_box(0));
lean_closure_set(v___x_2946_, 1, lean_box(0));
lean_closure_set(v___x_2946_, 2, v___x_2941_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___f_2942_);
v___x_2948_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2948_, 0, lean_box(0));
lean_closure_set(v___x_2948_, 1, lean_box(0));
lean_closure_set(v___x_2948_, 2, v___x_2941_);
v___x_2949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2947_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
lean_ctor_set(v___x_2949_, 2, v___f_2943_);
lean_ctor_set(v___x_2949_, 3, v___f_2944_);
lean_ctor_set(v___x_2949_, 4, v___f_2945_);
v___x_2950_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2950_, 0, lean_box(0));
lean_closure_set(v___x_2950_, 1, lean_box(0));
lean_closure_set(v___x_2950_, 2, v___x_2941_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
v___x_2954_ = l_instInhabitedOfMonad___redArg(v___x_2951_, v___x_2953_);
v___f_2955_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2955_, 0, v___x_2954_);
v___x_162765__overap_2956_ = lean_panic_fn_borrowed(v___f_2955_, v_msg_2937_);
lean_dec_ref(v___f_2955_);
lean_inc_ref(v___y_2938_);
v___x_2957_ = lean_apply_3(v___x_162765__overap_2956_, v___y_2938_, v___y_2939_, lean_box(0));
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2958_, v___y_2959_, v___y_2960_);
lean_dec_ref(v___y_2959_);
return v_res_2962_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2964_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0));
v___x_2965_ = lean_unsigned_to_nat(8u);
v___x_2966_ = lean_unsigned_to_nat(354u);
v___x_2967_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2968_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2969_ = l_mkPanicMessageWithDecl(v___x_2968_, v___x_2967_, v___x_2966_, v___x_2965_, v___x_2964_);
return v___x_2969_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2971_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2));
v___x_2972_ = lean_unsigned_to_nat(13u);
v___x_2973_ = lean_unsigned_to_nat(356u);
v___x_2974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2975_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2976_ = l_mkPanicMessageWithDecl(v___x_2975_, v___x_2974_, v___x_2973_, v___x_2972_, v___x_2971_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t v___x_2977_, lean_object* v_init_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_d_2984_; lean_object* v___y_2985_; 
if (lean_obj_tag(v_x_2979_) == 0)
{
lean_object* v_k_2989_; lean_object* v_l_2990_; lean_object* v_r_2991_; lean_object* v___x_2992_; 
v_k_2989_ = lean_ctor_get(v_x_2979_, 1);
lean_inc(v_k_2989_);
v_l_2990_ = lean_ctor_get(v_x_2979_, 3);
lean_inc(v_l_2990_);
v_r_2991_ = lean_ctor_get(v_x_2979_, 4);
lean_inc(v_r_2991_);
lean_dec_ref_known(v_x_2979_, 5);
v___x_2992_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_2977_, v_init_2978_, v_l_2990_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_fst_2994_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v_fst_2994_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_fst_2994_);
if (lean_obj_tag(v_fst_2994_) == 0)
{
lean_object* v_snd_2995_; lean_object* v_a_2996_; 
lean_dec(v_r_2991_);
lean_dec(v_k_2989_);
v_snd_2995_ = lean_ctor_get(v_a_2993_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_a_2993_);
v_a_2996_ = lean_ctor_get(v_fst_2994_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v_fst_2994_, 1);
v_d_2984_ = v_a_2996_;
v___y_2985_ = v_snd_2995_;
goto v___jp_2983_;
}
else
{
lean_object* v_snd_2997_; lean_object* v_a_2998_; lean_object* v___y_3000_; lean_object* v___y_3004_; lean_object* v___x_3030_; 
v_snd_2997_ = lean_ctor_get(v_a_2993_, 1);
lean_inc(v_snd_2997_);
lean_dec(v_a_2993_);
v_a_2998_ = lean_ctor_get(v_fst_2994_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v_fst_2994_, 1);
lean_inc_ref(v___y_2980_);
v___x_3030_ = l_Lean_Environment_find_x3f(v___y_2980_, v_k_2989_, v___x_2977_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_3032_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_3031_);
v___y_3004_ = v___x_3032_;
goto v___jp_3003_;
}
else
{
lean_object* v_val_3033_; 
v_val_3033_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_val_3033_);
lean_dec_ref_known(v___x_3030_, 1);
v___y_3004_ = v_val_3033_;
goto v___jp_3003_;
}
v___jp_2999_:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_array_push(v_a_2998_, v___y_3000_);
v_init_2978_ = v___x_3001_;
v_x_2979_ = v_r_2991_;
v___y_2981_ = v_snd_2997_;
goto _start;
}
v___jp_3003_:
{
if (lean_obj_tag(v___y_3004_) == 7)
{
lean_object* v_val_3005_; uint8_t v_isUnsafe_3006_; 
v_val_3005_ = lean_ctor_get(v___y_3004_, 0);
lean_inc_ref(v_val_3005_);
lean_dec_ref_known(v___y_3004_, 1);
v_isUnsafe_3006_ = lean_ctor_get_uint8(v_val_3005_, sizeof(void*)*7 + 1);
if (v_isUnsafe_3006_ == 0)
{
v___y_3000_ = v_val_3005_;
goto v___jp_2999_;
}
else
{
if (v___x_2977_ == 0)
{
uint8_t v_exportUnsafe_3007_; 
v_exportUnsafe_3007_ = lean_ctor_get_uint8(v_snd_2997_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref(v_val_3005_);
lean_dec(v_a_2998_);
v___x_3008_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1);
v___x_3009_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_3008_, v___y_2980_, v_snd_2997_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v_fst_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v_fst_3011_ = lean_ctor_get(v_a_3010_, 0);
lean_inc(v_fst_3011_);
if (lean_obj_tag(v_fst_3011_) == 0)
{
lean_object* v_snd_3012_; lean_object* v_a_3013_; 
lean_dec(v_r_2991_);
v_snd_3012_ = lean_ctor_get(v_a_3010_, 1);
lean_inc(v_snd_3012_);
lean_dec(v_a_3010_);
v_a_3013_ = lean_ctor_get(v_fst_3011_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v_fst_3011_, 1);
v_d_2984_ = v_a_3013_;
v___y_2985_ = v_snd_3012_;
goto v___jp_2983_;
}
else
{
lean_object* v_snd_3014_; lean_object* v_a_3015_; 
v_snd_3014_ = lean_ctor_get(v_a_3010_, 1);
lean_inc(v_snd_3014_);
lean_dec(v_a_3010_);
v_a_3015_ = lean_ctor_get(v_fst_3011_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v_fst_3011_, 1);
v_init_2978_ = v_a_3015_;
v_x_2979_ = v_r_2991_;
v___y_2981_ = v_snd_3014_;
goto _start;
}
}
else
{
lean_dec(v_r_2991_);
return v___x_3009_;
}
}
else
{
v___y_3000_ = v_val_3005_;
goto v___jp_2999_;
}
}
else
{
v___y_3000_ = v_val_3005_;
goto v___jp_2999_;
}
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec_ref(v___y_3004_);
v___x_3017_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3);
v___x_3018_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_3017_, v___y_2980_, v_snd_2997_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_snd_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_snd_3020_ = lean_ctor_get(v_a_3019_, 1);
lean_inc(v_snd_3020_);
lean_dec(v_a_3019_);
v_init_2978_ = v_a_2998_;
v_x_2979_ = v_r_2991_;
v___y_2981_ = v_snd_3020_;
goto _start;
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2998_);
lean_dec(v_r_2991_);
v_a_3022_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3018_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3018_);
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
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_dec(v_r_2991_);
lean_dec(v_k_2989_);
return v___x_2992_;
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_init_2978_);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___y_2981_);
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
v___jp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_d_2984_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v___y_2985_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object* v___x_3037_, lean_object* v_init_3038_, lean_object* v_x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v___x_172445__boxed_3043_; lean_object* v_res_3044_; 
v___x_172445__boxed_3043_ = lean_unbox(v___x_3037_);
v_res_3044_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_172445__boxed_3043_, v_init_3038_, v_x_3039_, v___y_3040_, v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t v_sz_3045_, size_t v_i_3046_, lean_object* v_bs_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_usize_dec_lt(v_i_3046_, v_sz_3045_);
if (v___x_3048_ == 0)
{
return v_bs_3047_;
}
else
{
lean_object* v_v_3049_; lean_object* v___x_3050_; lean_object* v_bs_x27_3051_; size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v_v_3049_ = lean_array_uget(v_bs_3047_, v_i_3046_);
v___x_3050_ = lean_unsigned_to_nat(0u);
v_bs_x27_3051_ = lean_array_uset(v_bs_3047_, v_i_3046_, v___x_3050_);
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_add(v_i_3046_, v___x_3052_);
v___x_3054_ = lean_array_uset(v_bs_x27_3051_, v_i_3046_, v_v_3049_);
v_i_3046_ = v___x_3053_;
v_bs_3047_ = v___x_3054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object* v_sz_3056_, lean_object* v_i_3057_, lean_object* v_bs_3058_){
_start:
{
size_t v_sz_boxed_3059_; size_t v_i_boxed_3060_; lean_object* v_res_3061_; 
v_sz_boxed_3059_ = lean_unbox_usize(v_sz_3056_);
lean_dec(v_sz_3056_);
v_i_boxed_3060_ = lean_unbox_usize(v_i_3057_);
lean_dec(v_i_3057_);
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_boxed_3059_, v_i_boxed_3060_, v_bs_3058_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object* v_a_3062_){
_start:
{
size_t v_sz_3063_; size_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_sz_3063_ = lean_array_size(v_a_3062_);
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_3063_, v___x_3064_, v_a_3062_);
v___x_3066_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_array_mk(v_a_3067_);
v___x_3069_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_3070_, size_t v_sz_3071_, size_t v_i_3072_, lean_object* v_b_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = lean_usize_dec_lt(v_i_3072_, v_sz_3071_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_b_3073_);
lean_ctor_set(v___x_3078_, 1, v___y_3075_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
else
{
lean_object* v_visitedNames_3080_; lean_object* v_visitedLevels_3081_; lean_object* v_visitedExprs_3082_; lean_object* v_visitedConstants_3083_; lean_object* v_noMDataExprs_3084_; uint8_t v_exportMData_3085_; uint8_t v_exportUnsafe_3086_; uint8_t v_ignoreMissing_3087_; lean_object* v_recursorMap_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3107_; 
v_visitedNames_3080_ = lean_ctor_get(v___y_3075_, 0);
v_visitedLevels_3081_ = lean_ctor_get(v___y_3075_, 1);
v_visitedExprs_3082_ = lean_ctor_get(v___y_3075_, 2);
v_visitedConstants_3083_ = lean_ctor_get(v___y_3075_, 3);
v_noMDataExprs_3084_ = lean_ctor_get(v___y_3075_, 4);
v_exportMData_3085_ = lean_ctor_get_uint8(v___y_3075_, sizeof(void*)*6);
v_exportUnsafe_3086_ = lean_ctor_get_uint8(v___y_3075_, sizeof(void*)*6 + 1);
v_ignoreMissing_3087_ = lean_ctor_get_uint8(v___y_3075_, sizeof(void*)*6 + 2);
v_recursorMap_3088_ = lean_ctor_get(v___y_3075_, 5);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___y_3075_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3090_ = v___y_3075_;
v_isShared_3091_ = v_isSharedCheck_3107_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_recursorMap_3088_);
lean_inc(v_noMDataExprs_3084_);
lean_inc(v_visitedConstants_3083_);
lean_inc(v_visitedExprs_3082_);
lean_inc(v_visitedLevels_3081_);
lean_inc(v_visitedNames_3080_);
lean_dec(v___y_3075_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3107_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_a_3092_; lean_object* v_toConstantVal_3093_; lean_object* v_name_3094_; lean_object* v_type_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v_a_3092_ = lean_array_uget_borrowed(v_as_3070_, v_i_3072_);
v_toConstantVal_3093_ = lean_ctor_get(v_a_3092_, 0);
v_name_3094_ = lean_ctor_get(v_toConstantVal_3093_, 0);
v_type_3095_ = lean_ctor_get(v_toConstantVal_3093_, 2);
v___x_3096_ = lean_box(0);
lean_inc(v_name_3094_);
v___x_3097_ = l_Lean_NameHashSet_insert(v_visitedConstants_3083_, v_name_3094_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 3, v___x_3097_);
v___x_3099_ = v___x_3090_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_visitedNames_3080_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_visitedLevels_3081_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_visitedExprs_3082_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3106_, 4, v_noMDataExprs_3084_);
lean_ctor_set(v_reuseFailAlloc_3106_, 5, v_recursorMap_3088_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*6, v_exportMData_3085_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*6 + 1, v_exportUnsafe_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*6 + 2, v_ignoreMissing_3087_);
v___x_3099_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; 
lean_inc_ref(v_type_3095_);
v___x_3100_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_3095_, v___y_3074_, v___x_3099_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v_snd_3102_; size_t v___x_3103_; size_t v___x_3104_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v_snd_3102_ = lean_ctor_get(v_a_3101_, 1);
lean_inc(v_snd_3102_);
lean_dec(v_a_3101_);
v___x_3103_ = ((size_t)1ULL);
v___x_3104_ = lean_usize_add(v_i_3072_, v___x_3103_);
v_i_3072_ = v___x_3104_;
v_b_3073_ = v___x_3096_;
v___y_3075_ = v_snd_3102_;
goto _start;
}
else
{
return v___x_3100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_3108_, lean_object* v_b_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
if (lean_obj_tag(v_as_x27_3108_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_b_3109_);
lean_ctor_set(v___x_3113_, 1, v___y_3111_);
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
else
{
lean_object* v_head_3115_; lean_object* v_tail_3116_; lean_object* v_rhs_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_head_3115_ = lean_ctor_get(v_as_x27_3108_, 0);
v_tail_3116_ = lean_ctor_get(v_as_x27_3108_, 1);
v_rhs_3117_ = lean_ctor_get(v_head_3115_, 2);
v___x_3118_ = lean_box(0);
lean_inc_ref(v_rhs_3117_);
v___x_3119_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_3117_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_snd_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v_snd_3121_ = lean_ctor_get(v_a_3120_, 1);
lean_inc(v_snd_3121_);
lean_dec(v_a_3120_);
v_as_x27_3108_ = v_tail_3116_;
v_b_3109_ = v___x_3118_;
v___y_3111_ = v_snd_3121_;
goto _start;
}
else
{
return v___x_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object* v_as_3123_, size_t v_sz_3124_, size_t v_i_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_3130_; 
v___x_3130_ = lean_usize_dec_lt(v_i_3125_, v_sz_3124_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_b_3126_);
lean_ctor_set(v___x_3131_, 1, v___y_3128_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
else
{
lean_object* v_a_3133_; lean_object* v_rules_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_a_3133_ = lean_array_uget_borrowed(v_as_3123_, v_i_3125_);
v_rules_3134_ = lean_ctor_get(v_a_3133_, 6);
v___x_3135_ = lean_box(0);
v___x_3136_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_3134_, v___x_3135_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v_snd_3138_; size_t v___x_3139_; size_t v___x_3140_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v_snd_3138_ = lean_ctor_get(v_a_3137_, 1);
lean_inc(v_snd_3138_);
lean_dec(v_a_3137_);
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3125_, v___x_3139_);
v_i_3125_ = v___x_3140_;
v_b_3126_ = v___x_3135_;
v___y_3128_ = v_snd_3138_;
goto _start;
}
else
{
return v___x_3136_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_unsigned_to_nat(16u);
v___x_3144_ = lean_mk_array(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3145_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_visitedConstants_3174_; lean_object* v_nat_3175_; uint8_t v___x_3176_; 
v_visitedConstants_3174_ = lean_ctor_get(v_a_3168_, 3);
v_nat_3175_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_3176_ = l_Lean_NameHashSet_contains(v_visitedConstants_3174_, v_nat_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
lean_inc_ref(v_a_3167_);
v___x_3177_ = l_Lean_Environment_find_x3f(v_a_3167_, v_nat_3175_, v___x_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
goto v___jp_3170_;
}
else
{
lean_object* v___x_3178_; 
lean_dec_ref_known(v___x_3177_, 1);
v___x_3178_ = l_LeanExport_dumpConstant(v_nat_3175_, v_a_3167_, v_a_3168_);
return v___x_3178_;
}
}
else
{
goto v___jp_3170_;
}
v___jp_3170_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v_a_3168_);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___y_3194_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v_visitedConstants_3201_; lean_object* v_visitedConstants_3206_; lean_object* v_charOfNat_3207_; uint8_t v___x_3208_; 
v_visitedConstants_3206_ = lean_ctor_get(v_a_3191_, 3);
v_charOfNat_3207_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_3208_ = l_Lean_NameHashSet_contains(v_visitedConstants_3206_, v_charOfNat_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; 
lean_inc_ref(v_a_3190_);
v___x_3209_ = l_Lean_Environment_find_x3f(v_a_3190_, v_charOfNat_3207_, v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_inc_ref(v_visitedConstants_3206_);
v___y_3199_ = v_a_3190_;
v___y_3200_ = v_a_3191_;
v_visitedConstants_3201_ = v_visitedConstants_3206_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3210_; 
lean_dec_ref_known(v___x_3209_, 1);
v___x_3210_ = l_LeanExport_dumpConstant(v_charOfNat_3207_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_snd_3212_; lean_object* v_visitedConstants_3213_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_snd_3212_ = lean_ctor_get(v_a_3211_, 1);
lean_inc(v_snd_3212_);
lean_dec(v_a_3211_);
v_visitedConstants_3213_ = lean_ctor_get(v_snd_3212_, 3);
lean_inc_ref(v_visitedConstants_3213_);
v___y_3199_ = v_a_3190_;
v___y_3200_ = v_snd_3212_;
v_visitedConstants_3201_ = v_visitedConstants_3213_;
goto v___jp_3198_;
}
else
{
return v___x_3210_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_3206_);
v___y_3199_ = v_a_3190_;
v___y_3200_ = v_a_3191_;
v_visitedConstants_3201_ = v_visitedConstants_3206_;
goto v___jp_3198_;
}
v___jp_3193_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v___y_3194_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
v___jp_3198_:
{
lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_3203_ = l_Lean_NameHashSet_contains(v_visitedConstants_3201_, v___x_3202_);
lean_dec_ref(v_visitedConstants_3201_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
lean_inc_ref(v___y_3199_);
v___x_3204_ = l_Lean_Environment_find_x3f(v___y_3199_, v___x_3202_, v___x_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
v___y_3194_ = v___y_3200_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3204_, 1);
v___x_3205_ = l_LeanExport_dumpConstant(v___x_3202_, v___y_3199_, v___y_3200_);
return v___x_3205_;
}
}
else
{
v___y_3194_ = v___y_3200_;
goto v___jp_3193_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3224_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_3225_ = lean_unsigned_to_nat(29u);
v___x_3226_ = lean_unsigned_to_nat(177u);
v___x_3227_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_3228_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_3229_ = l_mkPanicMessageWithDecl(v___x_3228_, v___x_3227_, v___x_3226_, v___x_3225_, v___x_3224_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_visitedNames_3234_; lean_object* v_visitedLevels_3235_; lean_object* v_visitedExprs_3236_; lean_object* v_visitedConstants_3237_; lean_object* v_noMDataExprs_3238_; uint8_t v_exportMData_3239_; uint8_t v_exportUnsafe_3240_; uint8_t v_ignoreMissing_3241_; lean_object* v_recursorMap_3242_; lean_object* v___x_3243_; 
v_visitedNames_3234_ = lean_ctor_get(v_a_3232_, 0);
v_visitedLevels_3235_ = lean_ctor_get(v_a_3232_, 1);
v_visitedExprs_3236_ = lean_ctor_get(v_a_3232_, 2);
v_visitedConstants_3237_ = lean_ctor_get(v_a_3232_, 3);
v_noMDataExprs_3238_ = lean_ctor_get(v_a_3232_, 4);
v_exportMData_3239_ = lean_ctor_get_uint8(v_a_3232_, sizeof(void*)*6);
v_exportUnsafe_3240_ = lean_ctor_get_uint8(v_a_3232_, sizeof(void*)*6 + 1);
v_ignoreMissing_3241_ = lean_ctor_get_uint8(v_a_3232_, sizeof(void*)*6 + 2);
v_recursorMap_3242_ = lean_ctor_get(v_a_3232_, 5);
v___x_3243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_3236_, v_e_3230_);
if (lean_obj_tag(v___x_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v_e_3230_);
v_val_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_val_3244_);
lean_ctor_set(v___x_3248_, 1, v_a_3232_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3248_);
v___x_3250_ = v___x_3246_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
else
{
lean_object* v___x_3253_; lean_object* v_fst_3255_; lean_object* v_visitedNames_3256_; lean_object* v_visitedLevels_3257_; lean_object* v_visitedExprs_3258_; lean_object* v_visitedConstants_3259_; lean_object* v_noMDataExprs_3260_; uint8_t v_exportMData_3261_; uint8_t v_exportUnsafe_3262_; uint8_t v_ignoreMissing_3263_; lean_object* v_recursorMap_3264_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; 
lean_dec(v___x_3243_);
v___x_3253_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_3230_))
{
case 0:
{
lean_object* v_deBruijnIndex_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_inc(v_recursorMap_3242_);
lean_inc_ref(v_noMDataExprs_3238_);
lean_inc_ref(v_visitedConstants_3237_);
lean_inc_ref(v_visitedExprs_3236_);
lean_inc_ref(v_visitedLevels_3235_);
lean_inc_ref(v_visitedNames_3234_);
lean_dec_ref(v_a_3232_);
v_deBruijnIndex_3302_ = lean_ctor_get(v_e_3230_, 0);
v___x_3303_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3302_);
v___x_3304_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3302_);
v___x_3305_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3303_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_Json_mkObj(v___x_3308_);
lean_dec_ref_known(v___x_3308_, 2);
v_fst_3255_ = v___x_3309_;
v_visitedNames_3256_ = v_visitedNames_3234_;
v_visitedLevels_3257_ = v_visitedLevels_3235_;
v_visitedExprs_3258_ = v_visitedExprs_3236_;
v_visitedConstants_3259_ = v_visitedConstants_3237_;
v_noMDataExprs_3260_ = v_noMDataExprs_3238_;
v_exportMData_3261_ = v_exportMData_3239_;
v_exportUnsafe_3262_ = v_exportUnsafe_3240_;
v_ignoreMissing_3263_ = v_ignoreMissing_3241_;
v_recursorMap_3264_ = v_recursorMap_3242_;
goto v___jp_3254_;
}
case 3:
{
lean_object* v_u_3310_; lean_object* v___x_3311_; 
v_u_3310_ = lean_ctor_get(v_e_3230_, 0);
lean_inc(v_u_3310_);
v___x_3311_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3310_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3333_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3333_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3333_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_fst_3316_; lean_object* v_snd_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3332_; 
v_fst_3316_ = lean_ctor_get(v_a_3312_, 0);
v_snd_3317_ = lean_ctor_get(v_a_3312_, 1);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_a_3312_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3319_ = v_a_3312_;
v_isShared_3320_ = v_isSharedCheck_3332_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_snd_3317_);
lean_inc(v_fst_3316_);
lean_dec(v_a_3312_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3332_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3321_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3322_ = l_Lean_JsonNumber_fromNat(v_fst_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 2);
lean_ctor_set(v___x_3314_, 0, v___x_3322_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3324_);
lean_ctor_set(v___x_3319_, 0, v___x_3321_);
v___x_3326_ = v___x_3319_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = l_Lean_Json_mkObj(v___x_3328_);
lean_dec_ref_known(v___x_3328_, 2);
v_fst_3291_ = v___x_3329_;
v_snd_3292_ = v_snd_3317_;
goto v___jp_3290_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 1);
return v___x_3311_;
}
}
case 4:
{
lean_object* v_declName_3334_; lean_object* v_us_3335_; lean_object* v___x_3336_; 
v_declName_3334_ = lean_ctor_get(v_e_3230_, 0);
v_us_3335_ = lean_ctor_get(v_e_3230_, 1);
lean_inc(v_declName_3334_);
v___x_3336_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3334_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3384_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3384_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3384_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_fst_3341_; lean_object* v_snd_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3383_; 
v_fst_3341_ = lean_ctor_get(v_a_3337_, 0);
v_snd_3342_ = lean_ctor_get(v_a_3337_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3337_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3344_ = v_a_3337_;
v_isShared_3345_ = v_isSharedCheck_3383_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3342_);
lean_inc(v_fst_3341_);
lean_dec(v_a_3337_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3383_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_box(0);
lean_inc(v_us_3335_);
v___x_3347_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3335_, v___x_3346_, v_a_3231_, v_snd_3342_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3374_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v_fst_3349_ = lean_ctor_get(v_a_3348_, 0);
v_snd_3350_ = lean_ctor_get(v_a_3348_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3348_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3352_ = v_a_3348_;
v_isShared_3353_ = v_isSharedCheck_3374_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3350_);
lean_inc(v_fst_3349_);
lean_dec(v_a_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3374_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3354_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3356_ = l_Lean_JsonNumber_fromNat(v_fst_3341_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set_tag(v___x_3339_, 2);
lean_ctor_set(v___x_3339_, 0, v___x_3356_);
v___x_3358_ = v___x_3339_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v___x_3358_);
lean_ctor_set(v___x_3352_, 0, v___x_3355_);
v___x_3360_ = v___x_3352_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3361_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3362_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3349_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v___x_3362_);
lean_ctor_set(v___x_3344_, 0, v___x_3361_);
v___x_3364_ = v___x_3344_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v___x_3346_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3360_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_Json_mkObj(v___x_3366_);
lean_dec_ref_known(v___x_3366_, 2);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3354_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3346_);
v___x_3370_ = l_Lean_Json_mkObj(v___x_3369_);
lean_dec_ref_known(v___x_3369_, 2);
v_fst_3291_ = v___x_3370_;
v_snd_3292_ = v_snd_3350_;
goto v___jp_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_del_object(v___x_3344_);
lean_dec(v_fst_3341_);
lean_del_object(v___x_3339_);
lean_dec_ref_known(v_e_3230_, 2);
v_a_3375_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3347_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3347_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 2);
return v___x_3336_;
}
}
case 5:
{
lean_object* v_fn_3385_; lean_object* v_arg_3386_; lean_object* v___x_3387_; 
v_fn_3385_ = lean_ctor_get(v_e_3230_, 0);
v_arg_3386_ = lean_ctor_get(v_e_3230_, 1);
lean_inc_ref(v_fn_3385_);
v___x_3387_ = l_LeanExport_dumpExprAux(v_fn_3385_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3434_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3434_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3434_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3433_; 
v_fst_3392_ = lean_ctor_get(v_a_3388_, 0);
v_snd_3393_ = lean_ctor_get(v_a_3388_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3395_ = v_a_3388_;
v_isShared_3396_ = v_isSharedCheck_3433_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snd_3393_);
lean_inc(v_fst_3392_);
lean_dec(v_a_3388_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3433_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; 
lean_inc_ref(v_arg_3386_);
v___x_3397_ = l_LeanExport_dumpExprAux(v_arg_3386_, v_a_3231_, v_snd_3393_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3432_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3432_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3432_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_fst_3402_; lean_object* v_snd_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3431_; 
v_fst_3402_ = lean_ctor_get(v_a_3398_, 0);
v_snd_3403_ = lean_ctor_get(v_a_3398_, 1);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3398_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3405_ = v_a_3398_;
v_isShared_3406_ = v_isSharedCheck_3431_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_snd_3403_);
lean_inc(v_fst_3402_);
lean_dec(v_a_3398_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3431_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3407_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3408_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3409_ = l_Lean_JsonNumber_fromNat(v_fst_3392_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 2);
lean_ctor_set(v___x_3400_, 0, v___x_3409_);
v___x_3411_ = v___x_3400_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3411_);
lean_ctor_set(v___x_3405_, 0, v___x_3408_);
v___x_3413_ = v___x_3405_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3414_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3415_ = l_Lean_JsonNumber_fromNat(v_fst_3402_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 2);
lean_ctor_set(v___x_3390_, 0, v___x_3415_);
v___x_3417_ = v___x_3390_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v___x_3417_);
lean_ctor_set(v___x_3395_, 0, v___x_3414_);
v___x_3419_ = v___x_3395_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3413_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = l_Lean_Json_mkObj(v___x_3422_);
lean_dec_ref_known(v___x_3422_, 2);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3407_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___x_3420_);
v___x_3426_ = l_Lean_Json_mkObj(v___x_3425_);
lean_dec_ref_known(v___x_3425_, 2);
v_fst_3291_ = v___x_3426_;
v_snd_3292_ = v_snd_3403_;
goto v___jp_3290_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3395_);
lean_dec(v_fst_3392_);
lean_del_object(v___x_3390_);
lean_dec_ref_known(v_e_3230_, 2);
return v___x_3397_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 2);
return v___x_3387_;
}
}
case 6:
{
lean_object* v_binderName_3435_; lean_object* v_binderType_3436_; lean_object* v_body_3437_; uint8_t v_binderInfo_3438_; lean_object* v___x_3439_; 
v_binderName_3435_ = lean_ctor_get(v_e_3230_, 0);
v_binderType_3436_ = lean_ctor_get(v_e_3230_, 1);
v_body_3437_ = lean_ctor_get(v_e_3230_, 2);
v_binderInfo_3438_ = lean_ctor_get_uint8(v_e_3230_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3435_);
v___x_3439_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3435_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3511_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3511_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3511_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3510_; 
v_fst_3444_ = lean_ctor_get(v_a_3440_, 0);
v_snd_3445_ = lean_ctor_get(v_a_3440_, 1);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3447_ = v_a_3440_;
v_isShared_3448_ = v_isSharedCheck_3510_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_inc(v_fst_3444_);
lean_dec(v_a_3440_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3510_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; 
lean_inc_ref(v_binderType_3436_);
v___x_3449_ = l_LeanExport_dumpExprAux(v_binderType_3436_, v_a_3231_, v_snd_3445_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3509_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3509_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3509_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_fst_3454_; lean_object* v_snd_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3508_; 
v_fst_3454_ = lean_ctor_get(v_a_3450_, 0);
v_snd_3455_ = lean_ctor_get(v_a_3450_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_a_3450_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3457_ = v_a_3450_;
v_isShared_3458_ = v_isSharedCheck_3508_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_snd_3455_);
lean_inc(v_fst_3454_);
lean_dec(v_a_3450_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3508_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; 
lean_inc_ref(v_body_3437_);
v___x_3459_ = l_LeanExport_dumpExprAux(v_body_3437_, v_a_3231_, v_snd_3455_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3507_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3507_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3507_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_fst_3464_; lean_object* v_snd_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3506_; 
v_fst_3464_ = lean_ctor_get(v_a_3460_, 0);
v_snd_3465_ = lean_ctor_get(v_a_3460_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_a_3460_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3467_ = v_a_3460_;
v_isShared_3468_ = v_isSharedCheck_3506_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_snd_3465_);
lean_inc(v_fst_3464_);
lean_dec(v_a_3460_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3506_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3469_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3471_ = l_Lean_JsonNumber_fromNat(v_fst_3444_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 2);
lean_ctor_set(v___x_3462_, 0, v___x_3471_);
v___x_3473_ = v___x_3462_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3473_);
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3475_ = v___x_3467_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3477_ = l_Lean_JsonNumber_fromNat(v_fst_3454_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set_tag(v___x_3452_, 2);
lean_ctor_set(v___x_3452_, 0, v___x_3477_);
v___x_3479_ = v___x_3452_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v___x_3479_);
lean_ctor_set(v___x_3457_, 0, v___x_3476_);
v___x_3481_ = v___x_3457_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3482_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3483_ = l_Lean_JsonNumber_fromNat(v_fst_3464_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 2);
lean_ctor_set(v___x_3442_, 0, v___x_3483_);
v___x_3485_ = v___x_3442_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3487_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3485_);
lean_ctor_set(v___x_3447_, 0, v___x_3482_);
v___x_3487_ = v___x_3447_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3488_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3489_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3438_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3487_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3481_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3475_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_Json_mkObj(v___x_3495_);
lean_dec_ref_known(v___x_3495_, 2);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3469_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___x_3491_);
v___x_3499_ = l_Lean_Json_mkObj(v___x_3498_);
lean_dec_ref_known(v___x_3498_, 2);
v_fst_3291_ = v___x_3499_;
v_snd_3292_ = v_snd_3465_;
goto v___jp_3290_;
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
lean_del_object(v___x_3457_);
lean_dec(v_fst_3454_);
lean_del_object(v___x_3452_);
lean_del_object(v___x_3447_);
lean_dec(v_fst_3444_);
lean_del_object(v___x_3442_);
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3459_;
}
}
}
}
else
{
lean_del_object(v___x_3447_);
lean_dec(v_fst_3444_);
lean_del_object(v___x_3442_);
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3449_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3439_;
}
}
case 7:
{
lean_object* v_binderName_3512_; lean_object* v_binderType_3513_; lean_object* v_body_3514_; uint8_t v_binderInfo_3515_; lean_object* v___x_3516_; 
v_binderName_3512_ = lean_ctor_get(v_e_3230_, 0);
v_binderType_3513_ = lean_ctor_get(v_e_3230_, 1);
v_body_3514_ = lean_ctor_get(v_e_3230_, 2);
v_binderInfo_3515_ = lean_ctor_get_uint8(v_e_3230_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3512_);
v___x_3516_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3512_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3588_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3588_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3588_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3587_; 
v_fst_3521_ = lean_ctor_get(v_a_3517_, 0);
v_snd_3522_ = lean_ctor_get(v_a_3517_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_a_3517_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3524_ = v_a_3517_;
v_isShared_3525_ = v_isSharedCheck_3587_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_a_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3587_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; 
lean_inc_ref(v_binderType_3513_);
v___x_3526_ = l_LeanExport_dumpExprAux(v_binderType_3513_, v_a_3231_, v_snd_3522_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3586_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3586_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3586_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_fst_3531_; lean_object* v_snd_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3585_; 
v_fst_3531_ = lean_ctor_get(v_a_3527_, 0);
v_snd_3532_ = lean_ctor_get(v_a_3527_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3527_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3534_ = v_a_3527_;
v_isShared_3535_ = v_isSharedCheck_3585_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_snd_3532_);
lean_inc(v_fst_3531_);
lean_dec(v_a_3527_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3585_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; 
lean_inc_ref(v_body_3514_);
v___x_3536_ = l_LeanExport_dumpExprAux(v_body_3514_, v_a_3231_, v_snd_3532_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3584_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3584_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3584_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_fst_3541_; lean_object* v_snd_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3583_; 
v_fst_3541_ = lean_ctor_get(v_a_3537_, 0);
v_snd_3542_ = lean_ctor_get(v_a_3537_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_a_3537_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3544_ = v_a_3537_;
v_isShared_3545_ = v_isSharedCheck_3583_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_snd_3542_);
lean_inc(v_fst_3541_);
lean_dec(v_a_3537_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3583_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3546_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3548_ = l_Lean_JsonNumber_fromNat(v_fst_3521_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 2);
lean_ctor_set(v___x_3539_, 0, v___x_3548_);
v___x_3550_ = v___x_3539_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___x_3550_);
lean_ctor_set(v___x_3544_, 0, v___x_3547_);
v___x_3552_ = v___x_3544_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3554_ = l_Lean_JsonNumber_fromNat(v_fst_3531_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 2);
lean_ctor_set(v___x_3529_, 0, v___x_3554_);
v___x_3556_ = v___x_3529_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3558_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 1, v___x_3556_);
lean_ctor_set(v___x_3534_, 0, v___x_3553_);
v___x_3558_ = v___x_3534_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3559_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3560_ = l_Lean_JsonNumber_fromNat(v_fst_3541_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 2);
lean_ctor_set(v___x_3519_, 0, v___x_3560_);
v___x_3562_ = v___x_3519_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3562_);
lean_ctor_set(v___x_3524_, 0, v___x_3559_);
v___x_3564_ = v___x_3524_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3565_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3566_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3515_);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_box(0);
v___x_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3564_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3558_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3552_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_Json_mkObj(v___x_3572_);
lean_dec_ref_known(v___x_3572_, 2);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3546_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v___x_3568_);
v___x_3576_ = l_Lean_Json_mkObj(v___x_3575_);
lean_dec_ref_known(v___x_3575_, 2);
v_fst_3291_ = v___x_3576_;
v_snd_3292_ = v_snd_3542_;
goto v___jp_3290_;
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
lean_del_object(v___x_3534_);
lean_dec(v_fst_3531_);
lean_del_object(v___x_3529_);
lean_del_object(v___x_3524_);
lean_dec(v_fst_3521_);
lean_del_object(v___x_3519_);
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3536_;
}
}
}
}
else
{
lean_del_object(v___x_3524_);
lean_dec(v_fst_3521_);
lean_del_object(v___x_3519_);
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3526_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3516_;
}
}
case 8:
{
lean_object* v_declName_3589_; lean_object* v_type_3590_; lean_object* v_value_3591_; lean_object* v_body_3592_; uint8_t v_nondep_3593_; lean_object* v___x_3594_; 
v_declName_3589_ = lean_ctor_get(v_e_3230_, 0);
v_type_3590_ = lean_ctor_get(v_e_3230_, 1);
v_value_3591_ = lean_ctor_get(v_e_3230_, 2);
v_body_3592_ = lean_ctor_get(v_e_3230_, 3);
v_nondep_3593_ = lean_ctor_get_uint8(v_e_3230_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3589_);
v___x_3594_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3589_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3687_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3687_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3687_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v_fst_3599_; lean_object* v_snd_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3686_; 
v_fst_3599_ = lean_ctor_get(v_a_3595_, 0);
v_snd_3600_ = lean_ctor_get(v_a_3595_, 1);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_a_3595_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3602_ = v_a_3595_;
v_isShared_3603_ = v_isSharedCheck_3686_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_snd_3600_);
lean_inc(v_fst_3599_);
lean_dec(v_a_3595_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3686_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; 
lean_inc_ref(v_type_3590_);
v___x_3604_ = l_LeanExport_dumpExprAux(v_type_3590_, v_a_3231_, v_snd_3600_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3685_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3685_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3685_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v_fst_3609_; lean_object* v_snd_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3684_; 
v_fst_3609_ = lean_ctor_get(v_a_3605_, 0);
v_snd_3610_ = lean_ctor_get(v_a_3605_, 1);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_a_3605_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3612_ = v_a_3605_;
v_isShared_3613_ = v_isSharedCheck_3684_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_snd_3610_);
lean_inc(v_fst_3609_);
lean_dec(v_a_3605_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3684_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; 
lean_inc_ref(v_value_3591_);
v___x_3614_ = l_LeanExport_dumpExprAux(v_value_3591_, v_a_3231_, v_snd_3610_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3683_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3683_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3683_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3682_; 
v_fst_3619_ = lean_ctor_get(v_a_3615_, 0);
v_snd_3620_ = lean_ctor_get(v_a_3615_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_a_3615_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3622_ = v_a_3615_;
v_isShared_3623_ = v_isSharedCheck_3682_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_snd_3620_);
lean_inc(v_fst_3619_);
lean_dec(v_a_3615_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3682_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; 
lean_inc_ref(v_body_3592_);
v___x_3624_ = l_LeanExport_dumpExprAux(v_body_3592_, v_a_3231_, v_snd_3620_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3681_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3681_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3681_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3680_; 
v_fst_3629_ = lean_ctor_get(v_a_3625_, 0);
v_snd_3630_ = lean_ctor_get(v_a_3625_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3625_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3632_ = v_a_3625_;
v_isShared_3633_ = v_isSharedCheck_3680_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_snd_3630_);
lean_inc(v_fst_3629_);
lean_dec(v_a_3625_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3680_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3634_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3636_ = l_Lean_JsonNumber_fromNat(v_fst_3599_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 2);
lean_ctor_set(v___x_3627_, 0, v___x_3636_);
v___x_3638_ = v___x_3627_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 1, v___x_3638_);
lean_ctor_set(v___x_3632_, 0, v___x_3635_);
v___x_3640_ = v___x_3632_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3641_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3642_ = l_Lean_JsonNumber_fromNat(v_fst_3609_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 2);
lean_ctor_set(v___x_3617_, 0, v___x_3642_);
v___x_3644_ = v___x_3617_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3646_; 
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 1, v___x_3644_);
lean_ctor_set(v___x_3622_, 0, v___x_3641_);
v___x_3646_ = v___x_3622_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3647_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3648_ = l_Lean_JsonNumber_fromNat(v_fst_3619_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 2);
lean_ctor_set(v___x_3607_, 0, v___x_3648_);
v___x_3650_ = v___x_3607_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v___x_3650_);
lean_ctor_set(v___x_3612_, 0, v___x_3647_);
v___x_3652_ = v___x_3612_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3653_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3654_ = l_Lean_JsonNumber_fromNat(v_fst_3629_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 2);
lean_ctor_set(v___x_3597_, 0, v___x_3654_);
v___x_3656_ = v___x_3597_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 1, v___x_3656_);
lean_ctor_set(v___x_3602_, 0, v___x_3653_);
v___x_3658_ = v___x_3602_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3659_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3660_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3660_, 0, v_nondep_3593_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3658_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3652_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3646_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3640_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = l_Lean_Json_mkObj(v___x_3667_);
lean_dec_ref_known(v___x_3667_, 2);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3634_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___x_3662_);
v___x_3671_ = l_Lean_Json_mkObj(v___x_3670_);
lean_dec_ref_known(v___x_3670_, 2);
v_fst_3291_ = v___x_3671_;
v_snd_3292_ = v_snd_3630_;
goto v___jp_3290_;
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
lean_del_object(v___x_3622_);
lean_dec(v_fst_3619_);
lean_del_object(v___x_3617_);
lean_del_object(v___x_3612_);
lean_dec(v_fst_3609_);
lean_del_object(v___x_3607_);
lean_del_object(v___x_3602_);
lean_dec(v_fst_3599_);
lean_del_object(v___x_3597_);
lean_dec_ref_known(v_e_3230_, 4);
return v___x_3624_;
}
}
}
}
else
{
lean_del_object(v___x_3612_);
lean_dec(v_fst_3609_);
lean_del_object(v___x_3607_);
lean_del_object(v___x_3602_);
lean_dec(v_fst_3599_);
lean_del_object(v___x_3597_);
lean_dec_ref_known(v_e_3230_, 4);
return v___x_3614_;
}
}
}
}
else
{
lean_del_object(v___x_3602_);
lean_dec(v_fst_3599_);
lean_del_object(v___x_3597_);
lean_dec_ref_known(v_e_3230_, 4);
return v___x_3604_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 4);
return v___x_3594_;
}
}
case 9:
{
lean_object* v_a_3688_; 
v_a_3688_ = lean_ctor_get(v_e_3230_, 0);
lean_inc_ref(v_a_3688_);
if (lean_obj_tag(v_a_3688_) == 0)
{
lean_object* v_val_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3720_; 
v_val_3689_ = lean_ctor_get(v_a_3688_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_a_3688_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3691_ = v_a_3688_;
v_isShared_3692_ = v_isSharedCheck_3720_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_val_3689_);
lean_dec(v_a_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3720_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; 
v___x_3693_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_snd_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3710_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_snd_3695_ = lean_ctor_get(v_a_3694_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v_a_3694_, 0);
lean_dec(v_unused_3711_);
v___x_3697_ = v_a_3694_;
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_snd_3695_);
lean_dec(v_a_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3699_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3700_ = l_Nat_reprFast(v_val_3689_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 3);
lean_ctor_set(v___x_3691_, 0, v___x_3700_);
v___x_3702_ = v___x_3691_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 1, v___x_3702_);
lean_ctor_set(v___x_3697_, 0, v___x_3699_);
v___x_3704_ = v___x_3697_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_Json_mkObj(v___x_3706_);
lean_dec_ref_known(v___x_3706_, 2);
v_fst_3291_ = v___x_3707_;
v_snd_3292_ = v_snd_3695_;
goto v___jp_3290_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3691_);
lean_dec(v_val_3689_);
lean_dec_ref_known(v_e_3230_, 1);
v_a_3712_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3693_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3693_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v_val_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3751_; 
v_val_3721_ = lean_ctor_get(v_a_3688_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_a_3688_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3723_ = v_a_3688_;
v_isShared_3724_ = v_isSharedCheck_3751_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_val_3721_);
lean_dec(v_a_3688_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3751_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; 
v___x_3725_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v_snd_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3741_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v_snd_3727_ = lean_ctor_get(v_a_3726_, 1);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; 
v_unused_3742_ = lean_ctor_get(v_a_3726_, 0);
lean_dec(v_unused_3742_);
v___x_3729_ = v_a_3726_;
v_isShared_3730_ = v_isSharedCheck_3741_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_snd_3727_);
lean_dec(v_a_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3741_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3731_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 3);
v___x_3733_ = v___x_3723_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_val_3721_);
v___x_3733_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 1, v___x_3733_);
lean_ctor_set(v___x_3729_, 0, v___x_3731_);
v___x_3735_ = v___x_3729_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = l_Lean_Json_mkObj(v___x_3737_);
lean_dec_ref_known(v___x_3737_, 2);
v_fst_3291_ = v___x_3738_;
v_snd_3292_ = v_snd_3727_;
goto v___jp_3290_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3723_);
lean_dec_ref(v_val_3721_);
lean_dec_ref_known(v_e_3230_, 1);
v_a_3743_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3725_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3725_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3752_; lean_object* v_expr_3753_; lean_object* v___x_3754_; 
v_data_3752_ = lean_ctor_get(v_e_3230_, 0);
v_expr_3753_ = lean_ctor_get(v_e_3230_, 1);
lean_inc_ref(v_expr_3753_);
v___x_3754_ = l_LeanExport_dumpExprAux(v_expr_3753_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3784_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3784_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3784_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_fst_3759_; lean_object* v_snd_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3783_; 
v_fst_3759_ = lean_ctor_get(v_a_3755_, 0);
v_snd_3760_ = lean_ctor_get(v_a_3755_, 1);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_a_3755_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3762_ = v_a_3755_;
v_isShared_3763_ = v_isSharedCheck_3783_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_snd_3760_);
lean_inc(v_fst_3759_);
lean_dec(v_a_3755_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3783_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3764_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3765_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3752_);
v___x_3766_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3752_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 1, v___x_3766_);
lean_ctor_set(v___x_3762_, 0, v___x_3765_);
v___x_3768_ = v___x_3762_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3769_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3770_ = l_Lean_JsonNumber_fromNat(v_fst_3759_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 2);
lean_ctor_set(v___x_3757_, 0, v___x_3770_);
v___x_3772_ = v___x_3757_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3769_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_box(0);
v___x_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3768_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = l_Lean_Json_mkObj(v___x_3776_);
lean_dec_ref_known(v___x_3776_, 2);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3764_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
lean_ctor_set(v___x_3779_, 1, v___x_3774_);
v___x_3780_ = l_Lean_Json_mkObj(v___x_3779_);
lean_dec_ref_known(v___x_3779_, 2);
v_fst_3291_ = v___x_3780_;
v_snd_3292_ = v_snd_3760_;
goto v___jp_3290_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 2);
return v___x_3754_;
}
}
case 11:
{
lean_object* v_typeName_3785_; lean_object* v_idx_3786_; lean_object* v_struct_3787_; lean_object* v___x_3788_; 
v_typeName_3785_ = lean_ctor_get(v_e_3230_, 0);
v_idx_3786_ = lean_ctor_get(v_e_3230_, 1);
v_struct_3787_ = lean_ctor_get(v_e_3230_, 2);
lean_inc(v_typeName_3785_);
v___x_3788_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3785_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3840_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3840_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3840_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_fst_3793_; lean_object* v_snd_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3839_; 
v_fst_3793_ = lean_ctor_get(v_a_3789_, 0);
v_snd_3794_ = lean_ctor_get(v_a_3789_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_a_3789_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3796_ = v_a_3789_;
v_isShared_3797_ = v_isSharedCheck_3839_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_snd_3794_);
lean_inc(v_fst_3793_);
lean_dec(v_a_3789_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3839_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; 
lean_inc_ref(v_struct_3787_);
v___x_3798_ = l_LeanExport_dumpExprAux(v_struct_3787_, v_a_3231_, v_snd_3794_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3838_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3838_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3838_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v_fst_3803_; lean_object* v_snd_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3837_; 
v_fst_3803_ = lean_ctor_get(v_a_3799_, 0);
v_snd_3804_ = lean_ctor_get(v_a_3799_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_a_3799_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3806_ = v_a_3799_;
v_isShared_3807_ = v_isSharedCheck_3837_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_snd_3804_);
lean_inc(v_fst_3803_);
lean_dec(v_a_3799_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3837_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3808_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3809_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3810_ = l_Lean_JsonNumber_fromNat(v_fst_3793_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set_tag(v___x_3801_, 2);
lean_ctor_set(v___x_3801_, 0, v___x_3810_);
v___x_3812_ = v___x_3801_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v___x_3812_);
lean_ctor_set(v___x_3806_, 0, v___x_3809_);
v___x_3814_ = v___x_3806_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3815_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3786_);
v___x_3816_ = l_Lean_JsonNumber_fromNat(v_idx_3786_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set_tag(v___x_3791_, 2);
lean_ctor_set(v___x_3791_, 0, v___x_3816_);
v___x_3818_ = v___x_3791_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3820_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 1, v___x_3818_);
lean_ctor_set(v___x_3796_, 0, v___x_3815_);
v___x_3820_ = v___x_3796_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3821_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3822_ = l_Lean_JsonNumber_fromNat(v_fst_3803_);
v___x_3823_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3821_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3820_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3814_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = l_Lean_Json_mkObj(v___x_3828_);
lean_dec_ref_known(v___x_3828_, 2);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3808_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
lean_ctor_set(v___x_3831_, 1, v___x_3825_);
v___x_3832_ = l_Lean_Json_mkObj(v___x_3831_);
lean_dec_ref_known(v___x_3831_, 2);
v_fst_3291_ = v___x_3832_;
v_snd_3292_ = v_snd_3804_;
goto v___jp_3290_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3796_);
lean_dec(v_fst_3793_);
lean_del_object(v___x_3791_);
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3798_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3230_, 3);
return v___x_3788_;
}
}
default: 
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3842_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3841_, v_a_3231_, v_a_3232_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v_fst_3844_; lean_object* v_snd_3845_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v_fst_3844_ = lean_ctor_get(v_a_3843_, 0);
lean_inc(v_fst_3844_);
v_snd_3845_ = lean_ctor_get(v_a_3843_, 1);
lean_inc(v_snd_3845_);
lean_dec(v_a_3843_);
v_fst_3291_ = v_fst_3844_;
v_snd_3292_ = v_snd_3845_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v_e_3230_);
v_a_3846_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3842_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3842_);
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
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
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
}
}
v___jp_3254_:
{
lean_object* v_size_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_size_3265_ = lean_ctor_get(v_visitedExprs_3258_, 0);
lean_inc_n(v_size_3265_, 2);
v___x_3266_ = l_Lean_JsonNumber_fromNat(v_size_3265_);
v___x_3267_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
v___x_3268_ = l_Lean_Json_setObjVal_x21(v_fst_3255_, v___x_3253_, v___x_3267_);
v___x_3269_ = l_Lean_Json_compress(v___x_3268_);
v___x_3270_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3280_; 
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
lean_object* v_unused_3281_; 
v_unused_3281_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3281_);
v___x_3272_ = v___x_3270_;
v_isShared_3273_ = v_isSharedCheck_3280_;
goto v_resetjp_3271_;
}
else
{
lean_dec(v___x_3270_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3280_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_inc(v_size_3265_);
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3258_, v_e_3230_, v_size_3265_);
v___x_3275_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3275_, 0, v_visitedNames_3256_);
lean_ctor_set(v___x_3275_, 1, v_visitedLevels_3257_);
lean_ctor_set(v___x_3275_, 2, v___x_3274_);
lean_ctor_set(v___x_3275_, 3, v_visitedConstants_3259_);
lean_ctor_set(v___x_3275_, 4, v_noMDataExprs_3260_);
lean_ctor_set(v___x_3275_, 5, v_recursorMap_3264_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*6, v_exportMData_3261_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*6 + 1, v_exportUnsafe_3262_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*6 + 2, v_ignoreMissing_3263_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_size_3265_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3276_);
v___x_3278_ = v___x_3272_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_size_3265_);
lean_dec(v_recursorMap_3264_);
lean_dec_ref(v_noMDataExprs_3260_);
lean_dec_ref(v_visitedConstants_3259_);
lean_dec_ref(v_visitedExprs_3258_);
lean_dec_ref(v_visitedLevels_3257_);
lean_dec_ref(v_visitedNames_3256_);
lean_dec_ref(v_e_3230_);
v_a_3282_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3270_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3270_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
v___jp_3290_:
{
lean_object* v_visitedNames_3293_; lean_object* v_visitedLevels_3294_; lean_object* v_visitedExprs_3295_; lean_object* v_visitedConstants_3296_; lean_object* v_noMDataExprs_3297_; uint8_t v_exportMData_3298_; uint8_t v_exportUnsafe_3299_; uint8_t v_ignoreMissing_3300_; lean_object* v_recursorMap_3301_; 
v_visitedNames_3293_ = lean_ctor_get(v_snd_3292_, 0);
lean_inc_ref(v_visitedNames_3293_);
v_visitedLevels_3294_ = lean_ctor_get(v_snd_3292_, 1);
lean_inc_ref(v_visitedLevels_3294_);
v_visitedExprs_3295_ = lean_ctor_get(v_snd_3292_, 2);
lean_inc_ref(v_visitedExprs_3295_);
v_visitedConstants_3296_ = lean_ctor_get(v_snd_3292_, 3);
lean_inc_ref(v_visitedConstants_3296_);
v_noMDataExprs_3297_ = lean_ctor_get(v_snd_3292_, 4);
lean_inc_ref(v_noMDataExprs_3297_);
v_exportMData_3298_ = lean_ctor_get_uint8(v_snd_3292_, sizeof(void*)*6);
v_exportUnsafe_3299_ = lean_ctor_get_uint8(v_snd_3292_, sizeof(void*)*6 + 1);
v_ignoreMissing_3300_ = lean_ctor_get_uint8(v_snd_3292_, sizeof(void*)*6 + 2);
v_recursorMap_3301_ = lean_ctor_get(v_snd_3292_, 5);
lean_inc(v_recursorMap_3301_);
lean_dec_ref(v_snd_3292_);
v_fst_3255_ = v_fst_3291_;
v_visitedNames_3256_ = v_visitedNames_3293_;
v_visitedLevels_3257_ = v_visitedLevels_3294_;
v_visitedExprs_3258_ = v_visitedExprs_3295_;
v_visitedConstants_3259_ = v_visitedConstants_3296_;
v_noMDataExprs_3260_ = v_noMDataExprs_3297_;
v_exportMData_3261_ = v_exportMData_3298_;
v_exportUnsafe_3262_ = v_exportUnsafe_3299_;
v_ignoreMissing_3263_ = v_ignoreMissing_3300_;
v_recursorMap_3264_ = v_recursorMap_3301_;
goto v___jp_3254_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
uint8_t v_exportMData_3858_; 
v_exportMData_3858_ = lean_ctor_get_uint8(v_a_3856_, sizeof(void*)*6);
if (v_exportMData_3858_ == 0)
{
lean_object* v_visitedNames_3859_; lean_object* v_visitedLevels_3860_; lean_object* v_visitedExprs_3861_; lean_object* v_visitedConstants_3862_; uint8_t v_exportUnsafe_3863_; uint8_t v_ignoreMissing_3864_; lean_object* v_recursorMap_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3886_; 
v_visitedNames_3859_ = lean_ctor_get(v_a_3856_, 0);
v_visitedLevels_3860_ = lean_ctor_get(v_a_3856_, 1);
v_visitedExprs_3861_ = lean_ctor_get(v_a_3856_, 2);
v_visitedConstants_3862_ = lean_ctor_get(v_a_3856_, 3);
v_exportUnsafe_3863_ = lean_ctor_get_uint8(v_a_3856_, sizeof(void*)*6 + 1);
v_ignoreMissing_3864_ = lean_ctor_get_uint8(v_a_3856_, sizeof(void*)*6 + 2);
v_recursorMap_3865_ = lean_ctor_get(v_a_3856_, 5);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_a_3856_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; 
v_unused_3887_ = lean_ctor_get(v_a_3856_, 4);
lean_dec(v_unused_3887_);
v___x_3867_ = v_a_3856_;
v_isShared_3868_ = v_isSharedCheck_3886_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_recursorMap_3865_);
lean_inc(v_visitedConstants_3862_);
lean_inc(v_visitedExprs_3861_);
lean_inc(v_visitedLevels_3860_);
lean_inc(v_visitedNames_3859_);
lean_dec(v_a_3856_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3886_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3869_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 4, v___x_3869_);
v___x_3871_ = v___x_3867_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_visitedNames_3859_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_visitedLevels_3860_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_visitedExprs_3861_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_visitedConstants_3862_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3885_, 5, v_recursorMap_3865_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*6, v_exportMData_3858_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*6 + 1, v_exportUnsafe_3863_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*6 + 2, v_ignoreMissing_3864_);
v___x_3871_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; 
v___x_3872_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3854_, v_a_3855_, v___x_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v_fst_3874_; lean_object* v_snd_3875_; lean_object* v___x_3876_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v_fst_3874_ = lean_ctor_get(v_a_3873_, 0);
lean_inc(v_fst_3874_);
v_snd_3875_ = lean_ctor_get(v_a_3873_, 1);
lean_inc(v_snd_3875_);
lean_dec(v_a_3873_);
v___x_3876_ = l_LeanExport_dumpExprAux(v_fst_3874_, v_a_3855_, v_snd_3875_);
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3872_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3872_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
else
{
lean_object* v___x_3888_; 
v___x_3888_ = l_LeanExport_dumpExprAux(v_e_3854_, v_a_3855_, v_a_3856_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t v_sz_3898_, size_t v_i_3899_, lean_object* v_bs_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
uint8_t v___x_3904_; 
v___x_3904_ = lean_usize_dec_lt(v_i_3899_, v_sz_3898_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v_bs_3900_);
lean_ctor_set(v___x_3905_, 1, v___y_3902_);
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
return v___x_3906_;
}
else
{
lean_object* v_v_3907_; lean_object* v_toConstantVal_3908_; lean_object* v_numParams_3909_; lean_object* v_numIndices_3910_; lean_object* v_all_3911_; lean_object* v_ctors_3912_; lean_object* v_numNested_3913_; uint8_t v_isRec_3914_; uint8_t v_isUnsafe_3915_; uint8_t v_isReflexive_3916_; lean_object* v_name_3917_; lean_object* v_levelParams_3918_; lean_object* v_type_3919_; lean_object* v___x_3920_; lean_object* v_bs_x27_3921_; lean_object* v___x_3922_; 
v_v_3907_ = lean_array_uget_borrowed(v_bs_3900_, v_i_3899_);
v_toConstantVal_3908_ = lean_ctor_get(v_v_3907_, 0);
v_numParams_3909_ = lean_ctor_get(v_v_3907_, 1);
lean_inc(v_numParams_3909_);
v_numIndices_3910_ = lean_ctor_get(v_v_3907_, 2);
lean_inc(v_numIndices_3910_);
v_all_3911_ = lean_ctor_get(v_v_3907_, 3);
lean_inc(v_all_3911_);
v_ctors_3912_ = lean_ctor_get(v_v_3907_, 4);
lean_inc(v_ctors_3912_);
v_numNested_3913_ = lean_ctor_get(v_v_3907_, 5);
lean_inc(v_numNested_3913_);
v_isRec_3914_ = lean_ctor_get_uint8(v_v_3907_, sizeof(void*)*6);
v_isUnsafe_3915_ = lean_ctor_get_uint8(v_v_3907_, sizeof(void*)*6 + 1);
v_isReflexive_3916_ = lean_ctor_get_uint8(v_v_3907_, sizeof(void*)*6 + 2);
v_name_3917_ = lean_ctor_get(v_toConstantVal_3908_, 0);
lean_inc(v_name_3917_);
v_levelParams_3918_ = lean_ctor_get(v_toConstantVal_3908_, 1);
lean_inc(v_levelParams_3918_);
v_type_3919_ = lean_ctor_get(v_toConstantVal_3908_, 2);
lean_inc_ref(v_type_3919_);
v___x_3920_ = lean_unsigned_to_nat(0u);
v_bs_x27_3921_ = lean_array_uset(v_bs_3900_, v_i_3899_, v___x_3920_);
v___x_3922_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3917_, v___y_3901_, v___y_3902_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v_fst_3924_; lean_object* v_snd_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_4055_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v_fst_3924_ = lean_ctor_get(v_a_3923_, 0);
v_snd_3925_ = lean_ctor_get(v_a_3923_, 1);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_a_3923_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_3927_ = v_a_3923_;
v_isShared_3928_ = v_isSharedCheck_4055_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snd_3925_);
lean_inc(v_fst_3924_);
lean_dec(v_a_3923_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_4055_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; 
v___x_3929_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3918_, v___y_3901_, v_snd_3925_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v_fst_3931_; lean_object* v_snd_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_4046_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v_fst_3931_ = lean_ctor_get(v_a_3930_, 0);
v_snd_3932_ = lean_ctor_get(v_a_3930_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_3934_ = v_a_3930_;
v_isShared_3935_ = v_isSharedCheck_4046_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_snd_3932_);
lean_inc(v_fst_3931_);
lean_dec(v_a_3930_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_4046_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_LeanExport_dumpExpr(v_type_3919_, v___y_3901_, v_snd_3932_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v_fst_3938_; lean_object* v_snd_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_4037_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v_fst_3938_ = lean_ctor_get(v_a_3937_, 0);
v_snd_3939_ = lean_ctor_get(v_a_3937_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_3937_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_3941_ = v_a_3937_;
v_isShared_3942_ = v_isSharedCheck_4037_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_snd_3939_);
lean_inc(v_fst_3938_);
lean_dec(v_a_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_4037_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; 
v___x_3943_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3911_, v___y_3901_, v_snd_3939_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4028_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_fst_3945_ = lean_ctor_get(v_a_3944_, 0);
v_snd_3946_ = lean_ctor_get(v_a_3944_, 1);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_a_3944_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_3948_ = v_a_3944_;
v_isShared_3949_ = v_isSharedCheck_4028_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_snd_3946_);
lean_inc(v_fst_3945_);
lean_dec(v_a_3944_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4028_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3912_, v___y_3901_, v_snd_3946_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_4019_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v_fst_3952_ = lean_ctor_get(v_a_3951_, 0);
v_snd_3953_ = lean_ctor_get(v_a_3951_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3955_ = v_a_3951_;
v_isShared_3956_ = v_isSharedCheck_4019_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_snd_3953_);
lean_inc(v_fst_3952_);
lean_dec(v_a_3951_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_4019_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3958_ = l_Lean_JsonNumber_fromNat(v_fst_3924_);
v___x_3959_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 1, v___x_3959_);
lean_ctor_set(v___x_3955_, 0, v___x_3957_);
v___x_3961_ = v___x_3955_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_4018_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v_fst_3931_);
lean_ctor_set(v___x_3948_, 0, v___x_3962_);
v___x_3964_ = v___x_3948_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_fst_3931_);
v___x_3964_ = v_reuseFailAlloc_4017_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3965_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3966_ = l_Lean_JsonNumber_fromNat(v_fst_3938_);
v___x_3967_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v___x_3967_);
lean_ctor_set(v___x_3941_, 0, v___x_3965_);
v___x_3969_ = v___x_3941_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_4016_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3971_ = l_Lean_JsonNumber_fromNat(v_numParams_3909_);
v___x_3972_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 1, v___x_3972_);
lean_ctor_set(v___x_3934_, 0, v___x_3970_);
v___x_3974_ = v___x_3934_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_4015_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_3976_ = l_Lean_JsonNumber_fromNat(v_numIndices_3910_);
v___x_3977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v___x_3977_);
lean_ctor_set(v___x_3927_, 0, v___x_3975_);
v___x_3979_ = v___x_3927_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_3975_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_4014_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v___x_3980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
lean_ctor_set(v___x_3981_, 1, v_fst_3945_);
v___x_3982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
lean_ctor_set(v___x_3983_, 1, v_fst_3952_);
v___x_3984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3));
v___x_3985_ = l_Lean_JsonNumber_fromNat(v_numNested_3913_);
v___x_3986_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3984_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4));
v___x_3989_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3989_, 0, v_isRec_3914_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5));
v___x_3992_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3992_, 0, v_isReflexive_3916_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3995_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3995_, 0, v_isUnsafe_3915_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3996_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3993_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3990_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3987_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_3983_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3981_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_3979_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_3974_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_3969_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
v___x_4007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_3964_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_3961_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v___x_4009_ = l_Lean_Json_mkObj(v___x_4008_);
lean_dec_ref_known(v___x_4008_, 2);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_3899_, v___x_4010_);
v___x_4012_ = lean_array_uset(v_bs_x27_3921_, v_i_3899_, v___x_4009_);
v_i_3899_ = v___x_4011_;
v_bs_3900_ = v___x_4012_;
v___y_3902_ = v_snd_3953_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_del_object(v___x_3948_);
lean_dec(v_fst_3945_);
lean_del_object(v___x_3941_);
lean_dec(v_fst_3938_);
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_del_object(v___x_3927_);
lean_dec(v_fst_3924_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec(v_numNested_3913_);
lean_dec(v_numIndices_3910_);
lean_dec(v_numParams_3909_);
v_a_4020_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_3950_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_3950_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_del_object(v___x_3941_);
lean_dec(v_fst_3938_);
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_del_object(v___x_3927_);
lean_dec(v_fst_3924_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec(v_numNested_3913_);
lean_dec(v_ctors_3912_);
lean_dec(v_numIndices_3910_);
lean_dec(v_numParams_3909_);
v_a_4029_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_3943_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_3943_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_del_object(v___x_3927_);
lean_dec(v_fst_3924_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec(v_numNested_3913_);
lean_dec(v_ctors_3912_);
lean_dec(v_all_3911_);
lean_dec(v_numIndices_3910_);
lean_dec(v_numParams_3909_);
v_a_4038_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_3936_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_3936_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_del_object(v___x_3927_);
lean_dec(v_fst_3924_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec_ref(v_type_3919_);
lean_dec(v_numNested_3913_);
lean_dec(v_ctors_3912_);
lean_dec(v_all_3911_);
lean_dec(v_numIndices_3910_);
lean_dec(v_numParams_3909_);
v_a_4047_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_3929_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_3929_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref(v_bs_x27_3921_);
lean_dec_ref(v_type_3919_);
lean_dec(v_levelParams_3918_);
lean_dec(v_numNested_3913_);
lean_dec(v_ctors_3912_);
lean_dec(v_all_3911_);
lean_dec(v_numIndices_3910_);
lean_dec(v_numParams_3909_);
v_a_4056_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_3922_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_3922_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t v_sz_4067_, size_t v_i_4068_, lean_object* v_bs_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = lean_usize_dec_lt(v_i_4068_, v_sz_4067_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4074_, 0, v_bs_4069_);
lean_ctor_set(v___x_4074_, 1, v___y_4071_);
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
}
else
{
lean_object* v_v_4076_; lean_object* v_toConstantVal_4077_; lean_object* v_induct_4078_; lean_object* v_cidx_4079_; lean_object* v_numParams_4080_; lean_object* v_numFields_4081_; uint8_t v_isUnsafe_4082_; lean_object* v_name_4083_; lean_object* v_levelParams_4084_; lean_object* v_type_4085_; lean_object* v___x_4086_; lean_object* v_bs_x27_4087_; lean_object* v___x_4088_; 
v_v_4076_ = lean_array_uget_borrowed(v_bs_4069_, v_i_4068_);
v_toConstantVal_4077_ = lean_ctor_get(v_v_4076_, 0);
v_induct_4078_ = lean_ctor_get(v_v_4076_, 1);
lean_inc(v_induct_4078_);
v_cidx_4079_ = lean_ctor_get(v_v_4076_, 2);
lean_inc(v_cidx_4079_);
v_numParams_4080_ = lean_ctor_get(v_v_4076_, 3);
lean_inc(v_numParams_4080_);
v_numFields_4081_ = lean_ctor_get(v_v_4076_, 4);
lean_inc(v_numFields_4081_);
v_isUnsafe_4082_ = lean_ctor_get_uint8(v_v_4076_, sizeof(void*)*5);
v_name_4083_ = lean_ctor_get(v_toConstantVal_4077_, 0);
lean_inc(v_name_4083_);
v_levelParams_4084_ = lean_ctor_get(v_toConstantVal_4077_, 1);
lean_inc(v_levelParams_4084_);
v_type_4085_ = lean_ctor_get(v_toConstantVal_4077_, 2);
lean_inc_ref(v_type_4085_);
v___x_4086_ = lean_unsigned_to_nat(0u);
v_bs_x27_4087_ = lean_array_uset(v_bs_4069_, v_i_4068_, v___x_4086_);
v___x_4088_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4083_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4194_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v_fst_4090_ = lean_ctor_get(v_a_4089_, 0);
v_snd_4091_ = lean_ctor_get(v_a_4089_, 1);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_a_4089_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4093_ = v_a_4089_;
v_isShared_4094_ = v_isSharedCheck_4194_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_snd_4091_);
lean_inc(v_fst_4090_);
lean_dec(v_a_4089_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4194_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; 
v___x_4095_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4084_, v___y_4070_, v_snd_4091_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_fst_4097_; lean_object* v_snd_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4185_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v_fst_4097_ = lean_ctor_get(v_a_4096_, 0);
v_snd_4098_ = lean_ctor_get(v_a_4096_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4100_ = v_a_4096_;
v_isShared_4101_ = v_isSharedCheck_4185_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_snd_4098_);
lean_inc(v_fst_4097_);
lean_dec(v_a_4096_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4185_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_LeanExport_dumpExpr(v_type_4085_, v___y_4070_, v_snd_4098_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v_fst_4104_; lean_object* v_snd_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4176_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
v_fst_4104_ = lean_ctor_get(v_a_4103_, 0);
v_snd_4105_ = lean_ctor_get(v_a_4103_, 1);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_a_4103_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4107_ = v_a_4103_;
v_isShared_4108_ = v_isSharedCheck_4176_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_snd_4105_);
lean_inc(v_fst_4104_);
lean_dec(v_a_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4176_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_4078_, v___y_4070_, v_snd_4105_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v_fst_4111_; lean_object* v_snd_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4167_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v_fst_4111_ = lean_ctor_get(v_a_4110_, 0);
v_snd_4112_ = lean_ctor_get(v_a_4110_, 1);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_a_4110_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4114_ = v_a_4110_;
v_isShared_4115_ = v_isSharedCheck_4167_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_snd_4112_);
lean_inc(v_fst_4111_);
lean_dec(v_a_4110_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4167_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4117_ = l_Lean_JsonNumber_fromNat(v_fst_4090_);
v___x_4118_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v___x_4118_);
lean_ctor_set(v___x_4114_, 0, v___x_4116_);
v___x_4120_ = v___x_4114_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4116_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 1, v_fst_4097_);
lean_ctor_set(v___x_4107_, 0, v___x_4121_);
v___x_4123_ = v___x_4107_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_fst_4097_);
v___x_4123_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4124_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4125_ = l_Lean_JsonNumber_fromNat(v_fst_4104_);
v___x_4126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 1, v___x_4126_);
lean_ctor_set(v___x_4100_, 0, v___x_4124_);
v___x_4128_ = v___x_4100_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2));
v___x_4130_ = l_Lean_JsonNumber_fromNat(v_fst_4111_);
v___x_4131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 1, v___x_4131_);
lean_ctor_set(v___x_4093_, 0, v___x_4129_);
v___x_4133_ = v___x_4093_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; size_t v___x_4159_; size_t v___x_4160_; lean_object* v___x_4161_; 
v___x_4134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3));
v___x_4135_ = l_Lean_JsonNumber_fromNat(v_cidx_4079_);
v___x_4136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4134_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_4139_ = l_Lean_JsonNumber_fromNat(v_numParams_4080_);
v___x_4140_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4138_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5));
v___x_4143_ = l_Lean_JsonNumber_fromNat(v_numFields_4081_);
v___x_4144_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4142_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4147_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4147_, 0, v_isUnsafe_4082_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4145_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4141_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4137_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4133_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4128_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4123_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4120_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_Json_mkObj(v___x_4157_);
lean_dec_ref_known(v___x_4157_, 2);
v___x_4159_ = ((size_t)1ULL);
v___x_4160_ = lean_usize_add(v_i_4068_, v___x_4159_);
v___x_4161_ = lean_array_uset(v_bs_x27_4087_, v_i_4068_, v___x_4158_);
v_i_4068_ = v___x_4160_;
v_bs_4069_ = v___x_4161_;
v___y_4071_ = v_snd_4112_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4107_);
lean_dec(v_fst_4104_);
lean_del_object(v___x_4100_);
lean_dec(v_fst_4097_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec(v_numFields_4081_);
lean_dec(v_numParams_4080_);
lean_dec(v_cidx_4079_);
v_a_4168_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4109_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4109_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_del_object(v___x_4100_);
lean_dec(v_fst_4097_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec(v_numFields_4081_);
lean_dec(v_numParams_4080_);
lean_dec(v_cidx_4079_);
lean_dec(v_induct_4078_);
v_a_4177_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4102_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4102_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_del_object(v___x_4093_);
lean_dec(v_fst_4090_);
lean_dec_ref(v_bs_x27_4087_);
lean_dec_ref(v_type_4085_);
lean_dec(v_numFields_4081_);
lean_dec(v_numParams_4080_);
lean_dec(v_cidx_4079_);
lean_dec(v_induct_4078_);
v_a_4186_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4095_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4095_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v_bs_x27_4087_);
lean_dec_ref(v_type_4085_);
lean_dec(v_levelParams_4084_);
lean_dec(v_numFields_4081_);
lean_dec(v_numParams_4080_);
lean_dec(v_cidx_4079_);
lean_dec(v_induct_4078_);
v_a_4195_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4088_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4088_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_ctor_4209_; lean_object* v_nfields_4210_; lean_object* v_rhs_4211_; lean_object* v___x_4212_; 
v_ctor_4209_ = lean_ctor_get(v_rule_4205_, 0);
lean_inc(v_ctor_4209_);
v_nfields_4210_ = lean_ctor_get(v_rule_4205_, 1);
lean_inc(v_nfields_4210_);
v_rhs_4211_ = lean_ctor_get(v_rule_4205_, 2);
lean_inc_ref(v_rhs_4211_);
lean_dec_ref(v_rule_4205_);
v___x_4212_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_4209_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v_fst_4214_; lean_object* v_snd_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4264_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v_fst_4214_ = lean_ctor_get(v_a_4213_, 0);
v_snd_4215_ = lean_ctor_get(v_a_4213_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_a_4213_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4217_ = v_a_4213_;
v_isShared_4218_ = v_isSharedCheck_4264_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_snd_4215_);
lean_inc(v_fst_4214_);
lean_dec(v_a_4213_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4264_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4219_; 
v___x_4219_ = l_LeanExport_dumpExpr(v_rhs_4211_, v_a_4206_, v_snd_4215_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4255_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4255_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4255_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v_fst_4224_; lean_object* v_snd_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4254_; 
v_fst_4224_ = lean_ctor_get(v_a_4220_, 0);
v_snd_4225_ = lean_ctor_get(v_a_4220_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_a_4220_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4227_ = v_a_4220_;
v_isShared_4228_ = v_isSharedCheck_4254_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_snd_4225_);
lean_inc(v_fst_4224_);
lean_dec(v_a_4220_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4254_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4229_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_4230_ = l_Lean_JsonNumber_fromNat(v_fst_4214_);
v___x_4231_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 1, v___x_4231_);
lean_ctor_set(v___x_4227_, 0, v___x_4229_);
v___x_4233_ = v___x_4227_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4234_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_4235_ = l_Lean_JsonNumber_fromNat(v_nfields_4210_);
v___x_4236_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 1, v___x_4236_);
lean_ctor_set(v___x_4217_, 0, v___x_4234_);
v___x_4238_ = v___x_4217_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4239_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_4240_ = l_Lean_JsonNumber_fromNat(v_fst_4224_);
v___x_4241_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4239_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4242_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4238_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4233_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Lean_Json_mkObj(v___x_4246_);
lean_dec_ref_known(v___x_4246_, 2);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v_snd_4225_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4248_);
v___x_4250_ = v___x_4222_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_del_object(v___x_4217_);
lean_dec(v_fst_4214_);
lean_dec(v_nfields_4210_);
v_a_4256_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4219_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4219_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec_ref(v_rhs_4211_);
lean_dec(v_nfields_4210_);
v_a_4265_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4212_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4212_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
if (lean_obj_tag(v_x_4273_) == 0)
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = l_List_reverse___redArg(v_x_4274_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
lean_ctor_set(v___x_4279_, 1, v___y_4276_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
else
{
lean_object* v_head_4281_; lean_object* v_tail_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4302_; 
v_head_4281_ = lean_ctor_get(v_x_4273_, 0);
v_tail_4282_ = lean_ctor_get(v_x_4273_, 1);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4273_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4284_ = v_x_4273_;
v_isShared_4285_ = v_isSharedCheck_4302_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_tail_4282_);
lean_inc(v_head_4281_);
lean_dec(v_x_4273_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4302_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4281_, v___y_4275_, v___y_4276_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; lean_object* v_fst_4288_; lean_object* v_snd_4289_; lean_object* v___x_4291_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4286_, 1);
v_fst_4288_ = lean_ctor_get(v_a_4287_, 0);
lean_inc(v_fst_4288_);
v_snd_4289_ = lean_ctor_get(v_a_4287_, 1);
lean_inc(v_snd_4289_);
lean_dec(v_a_4287_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 1, v_x_4274_);
lean_ctor_set(v___x_4284_, 0, v_fst_4288_);
v___x_4291_ = v___x_4284_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_fst_4288_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_x_4274_);
v___x_4291_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
v_x_4273_ = v_tail_4282_;
v_x_4274_ = v___x_4291_;
v___y_4276_ = v_snd_4289_;
goto _start;
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_del_object(v___x_4284_);
lean_dec(v_tail_4282_);
lean_dec(v_x_4274_);
v_a_4294_ = lean_ctor_get(v___x_4286_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4286_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4286_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_4307_, size_t v_i_4308_, lean_object* v_bs_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
uint8_t v___x_4313_; 
v___x_4313_ = lean_usize_dec_lt(v_i_4308_, v_sz_4307_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v_bs_4309_);
lean_ctor_set(v___x_4314_, 1, v___y_4311_);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
else
{
lean_object* v_v_4316_; lean_object* v_toConstantVal_4317_; lean_object* v_all_4318_; lean_object* v_numParams_4319_; lean_object* v_numIndices_4320_; lean_object* v_numMotives_4321_; lean_object* v_numMinors_4322_; lean_object* v_rules_4323_; uint8_t v_k_4324_; uint8_t v_isUnsafe_4325_; lean_object* v_name_4326_; lean_object* v_levelParams_4327_; lean_object* v_type_4328_; lean_object* v___x_4329_; lean_object* v_bs_x27_4330_; lean_object* v___x_4331_; 
v_v_4316_ = lean_array_uget_borrowed(v_bs_4309_, v_i_4308_);
v_toConstantVal_4317_ = lean_ctor_get(v_v_4316_, 0);
v_all_4318_ = lean_ctor_get(v_v_4316_, 1);
lean_inc(v_all_4318_);
v_numParams_4319_ = lean_ctor_get(v_v_4316_, 2);
lean_inc(v_numParams_4319_);
v_numIndices_4320_ = lean_ctor_get(v_v_4316_, 3);
lean_inc(v_numIndices_4320_);
v_numMotives_4321_ = lean_ctor_get(v_v_4316_, 4);
lean_inc(v_numMotives_4321_);
v_numMinors_4322_ = lean_ctor_get(v_v_4316_, 5);
lean_inc(v_numMinors_4322_);
v_rules_4323_ = lean_ctor_get(v_v_4316_, 6);
lean_inc(v_rules_4323_);
v_k_4324_ = lean_ctor_get_uint8(v_v_4316_, sizeof(void*)*7);
v_isUnsafe_4325_ = lean_ctor_get_uint8(v_v_4316_, sizeof(void*)*7 + 1);
v_name_4326_ = lean_ctor_get(v_toConstantVal_4317_, 0);
lean_inc(v_name_4326_);
v_levelParams_4327_ = lean_ctor_get(v_toConstantVal_4317_, 1);
lean_inc(v_levelParams_4327_);
v_type_4328_ = lean_ctor_get(v_toConstantVal_4317_, 2);
lean_inc_ref(v_type_4328_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v_bs_x27_4330_ = lean_array_uset(v_bs_4309_, v_i_4308_, v___x_4329_);
v___x_4331_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4326_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v_fst_4333_; lean_object* v_snd_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4466_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v_fst_4333_ = lean_ctor_get(v_a_4332_, 0);
v_snd_4334_ = lean_ctor_get(v_a_4332_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_a_4332_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4336_ = v_a_4332_;
v_isShared_4337_ = v_isSharedCheck_4466_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_snd_4334_);
lean_inc(v_fst_4333_);
lean_dec(v_a_4332_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4466_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4327_, v___y_4310_, v_snd_4334_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v_fst_4340_; lean_object* v_snd_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4457_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref_known(v___x_4338_, 1);
v_fst_4340_ = lean_ctor_get(v_a_4339_, 0);
v_snd_4341_ = lean_ctor_get(v_a_4339_, 1);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_a_4339_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4343_ = v_a_4339_;
v_isShared_4344_ = v_isSharedCheck_4457_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_snd_4341_);
lean_inc(v_fst_4340_);
lean_dec(v_a_4339_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4457_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_LeanExport_dumpExpr(v_type_4328_, v___y_4310_, v_snd_4341_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v_fst_4347_; lean_object* v_snd_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4448_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref_known(v___x_4345_, 1);
v_fst_4347_ = lean_ctor_get(v_a_4346_, 0);
v_snd_4348_ = lean_ctor_get(v_a_4346_, 1);
v_isSharedCheck_4448_ = !lean_is_exclusive(v_a_4346_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4350_ = v_a_4346_;
v_isShared_4351_ = v_isSharedCheck_4448_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_snd_4348_);
lean_inc(v_fst_4347_);
lean_dec(v_a_4346_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4448_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; 
v___x_4352_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4318_, v___y_4310_, v_snd_4348_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v_fst_4354_; lean_object* v_snd_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4439_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v_fst_4354_ = lean_ctor_get(v_a_4353_, 0);
v_snd_4355_ = lean_ctor_get(v_a_4353_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_a_4353_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4357_ = v_a_4353_;
v_isShared_4358_ = v_isSharedCheck_4439_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_snd_4355_);
lean_inc(v_fst_4354_);
lean_dec(v_a_4353_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4439_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = lean_box(0);
v___x_4360_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4323_, v___x_4359_, v___y_4310_, v_snd_4355_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v_fst_4362_; lean_object* v_snd_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4430_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v_fst_4362_ = lean_ctor_get(v_a_4361_, 0);
v_snd_4363_ = lean_ctor_get(v_a_4361_, 1);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_a_4361_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4365_ = v_a_4361_;
v_isShared_4366_ = v_isSharedCheck_4430_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_snd_4363_);
lean_inc(v_fst_4362_);
lean_dec(v_a_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4430_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4371_; 
v___x_4367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4368_ = l_Lean_JsonNumber_fromNat(v_fst_4333_);
v___x_4369_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 1, v___x_4369_);
lean_ctor_set(v___x_4365_, 0, v___x_4367_);
v___x_4371_ = v___x_4365_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v___x_4369_);
v___x_4371_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 1, v_fst_4340_);
lean_ctor_set(v___x_4357_, 0, v___x_4372_);
v___x_4374_ = v___x_4357_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_fst_4340_);
v___x_4374_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4375_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4376_ = l_Lean_JsonNumber_fromNat(v_fst_4347_);
v___x_4377_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 1, v___x_4377_);
lean_ctor_set(v___x_4350_, 0, v___x_4375_);
v___x_4379_ = v___x_4350_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4375_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 1, v_fst_4354_);
lean_ctor_set(v___x_4343_, 0, v___x_4380_);
v___x_4382_ = v___x_4343_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_fst_4354_);
v___x_4382_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_4384_ = l_Lean_JsonNumber_fromNat(v_numParams_4319_);
v___x_4385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 1, v___x_4385_);
lean_ctor_set(v___x_4336_, 0, v___x_4383_);
v___x_4387_ = v___x_4336_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; size_t v___x_4421_; size_t v___x_4422_; lean_object* v___x_4423_; 
v___x_4388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_4389_ = l_Lean_JsonNumber_fromNat(v_numIndices_4320_);
v___x_4390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4388_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4393_ = l_Lean_JsonNumber_fromNat(v_numMotives_4321_);
v___x_4394_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4392_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_4397_ = l_Lean_JsonNumber_fromNat(v_numMinors_4322_);
v___x_4398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
v___x_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4396_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4401_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4362_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4400_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_4404_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4404_, 0, v_k_4324_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4403_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v___x_4406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4407_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4407_, 0, v_isUnsafe_4325_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v___x_4359_);
v___x_4410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4405_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4402_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4399_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4395_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
v___x_4414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4391_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4387_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
v___x_4416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4382_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4379_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4374_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4371_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = l_Lean_Json_mkObj(v___x_4419_);
lean_dec_ref_known(v___x_4419_, 2);
v___x_4421_ = ((size_t)1ULL);
v___x_4422_ = lean_usize_add(v_i_4308_, v___x_4421_);
v___x_4423_ = lean_array_uset(v_bs_x27_4330_, v_i_4308_, v___x_4420_);
v_i_4308_ = v___x_4422_;
v_bs_4309_ = v___x_4423_;
v___y_4311_ = v_snd_4363_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_del_object(v___x_4357_);
lean_dec(v_fst_4354_);
lean_del_object(v___x_4350_);
lean_dec(v_fst_4347_);
lean_del_object(v___x_4343_);
lean_dec(v_fst_4340_);
lean_del_object(v___x_4336_);
lean_dec(v_fst_4333_);
lean_dec_ref(v_bs_x27_4330_);
lean_dec(v_numMinors_4322_);
lean_dec(v_numMotives_4321_);
lean_dec(v_numIndices_4320_);
lean_dec(v_numParams_4319_);
v_a_4431_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4360_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4360_);
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
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_del_object(v___x_4350_);
lean_dec(v_fst_4347_);
lean_del_object(v___x_4343_);
lean_dec(v_fst_4340_);
lean_del_object(v___x_4336_);
lean_dec(v_fst_4333_);
lean_dec_ref(v_bs_x27_4330_);
lean_dec(v_rules_4323_);
lean_dec(v_numMinors_4322_);
lean_dec(v_numMotives_4321_);
lean_dec(v_numIndices_4320_);
lean_dec(v_numParams_4319_);
v_a_4440_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4352_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4352_);
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
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_del_object(v___x_4343_);
lean_dec(v_fst_4340_);
lean_del_object(v___x_4336_);
lean_dec(v_fst_4333_);
lean_dec_ref(v_bs_x27_4330_);
lean_dec(v_rules_4323_);
lean_dec(v_numMinors_4322_);
lean_dec(v_numMotives_4321_);
lean_dec(v_numIndices_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_all_4318_);
v_a_4449_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4345_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4345_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4336_);
lean_dec(v_fst_4333_);
lean_dec_ref(v_bs_x27_4330_);
lean_dec_ref(v_type_4328_);
lean_dec(v_rules_4323_);
lean_dec(v_numMinors_4322_);
lean_dec(v_numMotives_4321_);
lean_dec(v_numIndices_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_all_4318_);
v_a_4458_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4338_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4338_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec_ref(v_bs_x27_4330_);
lean_dec_ref(v_type_4328_);
lean_dec(v_levelParams_4327_);
lean_dec(v_rules_4323_);
lean_dec(v_numMinors_4322_);
lean_dec(v_numMotives_4321_);
lean_dec(v_numIndices_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_all_4318_);
v_a_4467_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4331_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4331_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4523_, lean_object* v_as_x27_4524_, lean_object* v_b_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
if (lean_obj_tag(v_as_x27_4524_) == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v_b_4525_);
lean_ctor_set(v___x_4529_, 1, v___y_4527_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
else
{
lean_object* v_head_4531_; lean_object* v_tail_4532_; lean_object* v___x_4533_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___x_4564_; 
lean_dec_ref(v_b_4525_);
v_head_4531_ = lean_ctor_get(v_as_x27_4524_, 0);
v_tail_4532_ = lean_ctor_get(v_as_x27_4524_, 1);
v___x_4533_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4531_);
lean_inc_ref(v___y_4526_);
v___x_4564_ = l_Lean_Environment_find_x3f(v___y_4526_, v_head_4531_, v___x_4523_);
if (lean_obj_tag(v___x_4564_) == 1)
{
lean_object* v_val_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4688_; 
v_val_4565_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4567_ = v___x_4564_;
v_isShared_4568_ = v_isSharedCheck_4688_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_val_4565_);
lean_dec(v___x_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4688_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
if (lean_obj_tag(v_val_4565_) == 4)
{
lean_object* v_val_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4687_; 
v_val_4569_ = lean_ctor_get(v_val_4565_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_val_4565_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4571_ = v_val_4565_;
v_isShared_4572_ = v_isSharedCheck_4687_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_val_4569_);
lean_dec(v_val_4565_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4687_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v_toConstantVal_4573_; lean_object* v_visitedNames_4574_; lean_object* v_visitedLevels_4575_; lean_object* v_visitedExprs_4576_; lean_object* v_visitedConstants_4577_; lean_object* v_noMDataExprs_4578_; uint8_t v_exportMData_4579_; uint8_t v_exportUnsafe_4580_; uint8_t v_ignoreMissing_4581_; lean_object* v_recursorMap_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4686_; 
v_toConstantVal_4573_ = lean_ctor_get(v_val_4569_, 0);
lean_inc_ref(v_toConstantVal_4573_);
v_visitedNames_4574_ = lean_ctor_get(v___y_4527_, 0);
v_visitedLevels_4575_ = lean_ctor_get(v___y_4527_, 1);
v_visitedExprs_4576_ = lean_ctor_get(v___y_4527_, 2);
v_visitedConstants_4577_ = lean_ctor_get(v___y_4527_, 3);
v_noMDataExprs_4578_ = lean_ctor_get(v___y_4527_, 4);
v_exportMData_4579_ = lean_ctor_get_uint8(v___y_4527_, sizeof(void*)*6);
v_exportUnsafe_4580_ = lean_ctor_get_uint8(v___y_4527_, sizeof(void*)*6 + 1);
v_ignoreMissing_4581_ = lean_ctor_get_uint8(v___y_4527_, sizeof(void*)*6 + 2);
v_recursorMap_4582_ = lean_ctor_get(v___y_4527_, 5);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___y_4527_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4584_ = v___y_4527_;
v_isShared_4585_ = v_isSharedCheck_4686_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_recursorMap_4582_);
lean_inc(v_noMDataExprs_4578_);
lean_inc(v_visitedConstants_4577_);
lean_inc(v_visitedExprs_4576_);
lean_inc(v_visitedLevels_4575_);
lean_inc(v_visitedNames_4574_);
lean_dec(v___y_4527_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4686_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
uint8_t v_kind_4586_; lean_object* v_name_4587_; lean_object* v_levelParams_4588_; lean_object* v_type_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v_kind_4586_ = lean_ctor_get_uint8(v_val_4569_, sizeof(void*)*1);
lean_dec_ref(v_val_4569_);
v_name_4587_ = lean_ctor_get(v_toConstantVal_4573_, 0);
lean_inc(v_name_4587_);
v_levelParams_4588_ = lean_ctor_get(v_toConstantVal_4573_, 1);
lean_inc(v_levelParams_4588_);
v_type_4589_ = lean_ctor_get(v_toConstantVal_4573_, 2);
lean_inc_ref(v_type_4589_);
lean_dec_ref(v_toConstantVal_4573_);
lean_inc(v_head_4531_);
v___x_4590_ = l_Lean_NameHashSet_insert(v_visitedConstants_4577_, v_head_4531_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 3, v___x_4590_);
v___x_4592_ = v___x_4584_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_visitedNames_4574_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_visitedLevels_4575_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_visitedExprs_4576_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_noMDataExprs_4578_);
lean_ctor_set(v_reuseFailAlloc_4685_, 5, v_recursorMap_4582_);
lean_ctor_set_uint8(v_reuseFailAlloc_4685_, sizeof(void*)*6, v_exportMData_4579_);
lean_ctor_set_uint8(v_reuseFailAlloc_4685_, sizeof(void*)*6 + 1, v_exportUnsafe_4580_);
lean_ctor_set_uint8(v_reuseFailAlloc_4685_, sizeof(void*)*6 + 2, v_ignoreMissing_4581_);
v___x_4592_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; 
v___x_4593_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4587_, v___y_4526_, v___x_4592_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v_fst_4595_; lean_object* v_snd_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4676_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4593_, 1);
v_fst_4595_ = lean_ctor_get(v_a_4594_, 0);
v_snd_4596_ = lean_ctor_get(v_a_4594_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_a_4594_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4598_ = v_a_4594_;
v_isShared_4599_ = v_isSharedCheck_4676_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_snd_4596_);
lean_inc(v_fst_4595_);
lean_dec(v_a_4594_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4676_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; 
v___x_4600_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4588_, v___y_4526_, v_snd_4596_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v_fst_4602_; lean_object* v_snd_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4667_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4600_, 1);
v_fst_4602_ = lean_ctor_get(v_a_4601_, 0);
v_snd_4603_ = lean_ctor_get(v_a_4601_, 1);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_a_4601_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4605_ = v_a_4601_;
v_isShared_4606_ = v_isSharedCheck_4667_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_snd_4603_);
lean_inc(v_fst_4602_);
lean_dec(v_a_4601_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4667_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_LeanExport_dumpExpr(v_type_4589_, v___y_4526_, v_snd_4603_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v_fst_4609_; lean_object* v_snd_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4658_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4607_, 1);
v_fst_4609_ = lean_ctor_get(v_a_4608_, 0);
v_snd_4610_ = lean_ctor_get(v_a_4608_, 1);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_a_4608_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4612_ = v_a_4608_;
v_isShared_4613_ = v_isSharedCheck_4658_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_snd_4610_);
lean_inc(v_fst_4609_);
lean_dec(v_a_4608_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4658_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4614_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4616_ = l_Lean_JsonNumber_fromNat(v_fst_4595_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set_tag(v___x_4571_, 2);
lean_ctor_set(v___x_4571_, 0, v___x_4616_);
v___x_4618_ = v___x_4571_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4620_; 
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 1, v___x_4618_);
lean_ctor_set(v___x_4612_, 0, v___x_4615_);
v___x_4620_ = v___x_4612_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 1, v_fst_4602_);
lean_ctor_set(v___x_4605_, 0, v___x_4621_);
v___x_4623_ = v___x_4605_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_fst_4602_);
v___x_4623_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4624_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4625_ = l_Lean_JsonNumber_fromNat(v_fst_4609_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set_tag(v___x_4567_, 2);
lean_ctor_set(v___x_4567_, 0, v___x_4625_);
v___x_4627_ = v___x_4567_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
lean_object* v___x_4629_; 
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 1, v___x_4627_);
lean_ctor_set(v___x_4598_, 0, v___x_4624_);
v___x_4629_ = v___x_4598_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4630_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4631_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4586_);
v___x_4632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
v___x_4633_ = lean_box(0);
v___x_4634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4632_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4629_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
v___x_4636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4623_);
lean_ctor_set(v___x_4636_, 1, v___x_4635_);
v___x_4637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4620_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = l_Lean_Json_mkObj(v___x_4637_);
lean_dec_ref_known(v___x_4637_, 2);
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4614_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4633_);
v___x_4641_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4640_, v_snd_4610_);
lean_dec_ref_known(v___x_4640_, 2);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; lean_object* v_snd_4643_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref_known(v___x_4641_, 1);
v_snd_4643_ = lean_ctor_get(v_a_4642_, 1);
lean_inc(v_snd_4643_);
lean_dec(v_a_4642_);
v_as_x27_4524_ = v_tail_4532_;
v_b_4525_ = v___x_4533_;
v___y_4527_ = v_snd_4643_;
goto _start;
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
v_a_4645_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4641_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4641_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
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
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_del_object(v___x_4605_);
lean_dec(v_fst_4602_);
lean_del_object(v___x_4598_);
lean_dec(v_fst_4595_);
lean_del_object(v___x_4571_);
lean_del_object(v___x_4567_);
v_a_4659_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4607_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4607_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_del_object(v___x_4598_);
lean_dec(v_fst_4595_);
lean_dec_ref(v_type_4589_);
lean_del_object(v___x_4571_);
lean_del_object(v___x_4567_);
v_a_4668_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4600_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4600_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v_type_4589_);
lean_dec(v_levelParams_4588_);
lean_del_object(v___x_4571_);
lean_del_object(v___x_4567_);
v_a_4677_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4593_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4593_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4567_);
lean_dec(v_val_4565_);
v___y_4535_ = v___y_4526_;
v___y_4536_ = v___y_4527_;
goto v___jp_4534_;
}
}
}
else
{
lean_dec(v___x_4564_);
v___y_4535_ = v___y_4526_;
v___y_4536_ = v___y_4527_;
goto v___jp_4534_;
}
v___jp_4534_:
{
uint8_t v_ignoreMissing_4537_; 
v_ignoreMissing_4537_ = lean_ctor_get_uint8(v___y_4536_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4537_ == 0)
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4538_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4539_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4540_ = lean_unsigned_to_nat(313u);
v___x_4541_ = lean_unsigned_to_nat(52u);
v___x_4542_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4543_ = 1;
lean_inc(v_head_4531_);
v___x_4544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4531_, v___x_4543_);
v___x_4545_ = lean_string_append(v___x_4542_, v___x_4544_);
lean_dec_ref(v___x_4544_);
v___x_4546_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4547_ = lean_string_append(v___x_4545_, v___x_4546_);
v___x_4548_ = l_mkPanicMessageWithDecl(v___x_4538_, v___x_4539_, v___x_4540_, v___x_4541_, v___x_4547_);
lean_dec_ref(v___x_4547_);
v___x_4549_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4548_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v_snd_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_snd_4551_ = lean_ctor_get(v_a_4550_, 1);
lean_inc(v_snd_4551_);
lean_dec(v_a_4550_);
v_as_x27_4524_ = v_tail_4532_;
v_b_4525_ = v___x_4533_;
v___y_4527_ = v_snd_4551_;
goto _start;
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
v_a_4553_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4549_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4549_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
lean_ctor_set(v___x_4562_, 1, v___y_4536_);
v___x_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
return v___x_4563_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = l_Lean_NameSet_empty;
v___x_4692_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v___x_4691_);
return v___x_4693_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4694_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4695_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4695_);
lean_ctor_set(v___x_4696_, 1, v___x_4694_);
return v___x_4696_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4700_ = lean_unsigned_to_nat(11u);
v___x_4701_ = lean_unsigned_to_nat(341u);
v___x_4702_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4703_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4704_ = l_mkPanicMessageWithDecl(v___x_4703_, v___x_4702_, v___x_4701_, v___x_4700_, v___x_4699_);
return v___x_4704_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4706_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4707_ = lean_unsigned_to_nat(6u);
v___x_4708_ = lean_unsigned_to_nat(329u);
v___x_4709_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4710_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4711_ = l_mkPanicMessageWithDecl(v___x_4710_, v___x_4709_, v___x_4708_, v___x_4707_, v___x_4706_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4712_, lean_object* v_val_4713_, lean_object* v_as_x27_4714_, lean_object* v_b_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
if (lean_obj_tag(v_as_x27_4714_) == 0)
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_b_4715_);
lean_ctor_set(v___x_4719_, 1, v___y_4717_);
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
return v___x_4720_;
}
else
{
lean_object* v_head_4721_; lean_object* v_tail_4722_; lean_object* v___y_4724_; lean_object* v_snd_4755_; lean_object* v_fst_4756_; lean_object* v_fst_4757_; lean_object* v_snd_4758_; lean_object* v___y_4760_; lean_object* v_toConstantVal_4761_; lean_object* v_ctors_4762_; uint8_t v___y_4763_; lean_object* v___y_4842_; lean_object* v___x_4853_; 
v_head_4721_ = lean_ctor_get(v_as_x27_4714_, 0);
v_tail_4722_ = lean_ctor_get(v_as_x27_4714_, 1);
v_snd_4755_ = lean_ctor_get(v_b_4715_, 1);
lean_inc(v_snd_4755_);
v_fst_4756_ = lean_ctor_get(v_b_4715_, 0);
lean_inc(v_fst_4756_);
lean_dec_ref(v_b_4715_);
v_fst_4757_ = lean_ctor_get(v_snd_4755_, 0);
lean_inc(v_fst_4757_);
v_snd_4758_ = lean_ctor_get(v_snd_4755_, 1);
lean_inc(v_snd_4758_);
lean_dec(v_snd_4755_);
lean_inc(v_head_4721_);
lean_inc_ref(v___y_4716_);
v___x_4853_ = l_Lean_Environment_find_x3f(v___y_4716_, v_head_4721_, v___x_4712_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_4855_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4854_);
v___y_4842_ = v___x_4855_;
goto v___jp_4841_;
}
else
{
lean_object* v_val_4856_; 
v_val_4856_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_val_4856_);
lean_dec_ref_known(v___x_4853_, 1);
v___y_4842_ = v_val_4856_;
goto v___jp_4841_;
}
v___jp_4723_:
{
if (lean_obj_tag(v___y_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4746_; 
v_a_4725_ = lean_ctor_get(v___y_4724_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___y_4724_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4727_ = v___y_4724_;
v_isShared_4728_ = v_isSharedCheck_4746_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___y_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4746_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v_fst_4729_; 
v_fst_4729_ = lean_ctor_get(v_a_4725_, 0);
lean_inc(v_fst_4729_);
if (lean_obj_tag(v_fst_4729_) == 0)
{
lean_object* v_snd_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4741_; 
v_snd_4730_ = lean_ctor_get(v_a_4725_, 1);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_a_4725_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; 
v_unused_4742_ = lean_ctor_get(v_a_4725_, 0);
lean_dec(v_unused_4742_);
v___x_4732_ = v_a_4725_;
v_isShared_4733_ = v_isSharedCheck_4741_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_snd_4730_);
lean_dec(v_a_4725_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4741_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v_a_4734_; lean_object* v___x_4736_; 
v_a_4734_ = lean_ctor_get(v_fst_4729_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v_fst_4729_, 1);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v_a_4734_);
v___x_4736_ = v___x_4732_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_snd_4730_);
v___x_4736_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4738_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4736_);
v___x_4738_ = v___x_4727_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_snd_4743_; lean_object* v_a_4744_; 
lean_del_object(v___x_4727_);
v_snd_4743_ = lean_ctor_get(v_a_4725_, 1);
lean_inc(v_snd_4743_);
lean_dec(v_a_4725_);
v_a_4744_ = lean_ctor_get(v_fst_4729_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v_fst_4729_, 1);
v_as_x27_4714_ = v_tail_4722_;
v_b_4715_ = v_a_4744_;
v___y_4717_ = v_snd_4743_;
goto _start;
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4747_ = lean_ctor_get(v___y_4724_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___y_4724_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___y_4724_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___y_4724_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
v___jp_4759_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = lean_array_push(v_fst_4756_, v___y_4760_);
v___x_4765_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4763_, v___x_4712_, v_ctors_4762_, v_fst_4757_, v___y_4716_, v___y_4717_);
lean_dec(v_ctors_4762_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v_snd_4767_; lean_object* v_fst_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4832_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
v_snd_4767_ = lean_ctor_get(v_a_4766_, 1);
v_fst_4768_ = lean_ctor_get(v_a_4766_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v_a_4766_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4770_ = v_a_4766_;
v_isShared_4771_ = v_isSharedCheck_4832_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_snd_4767_);
lean_inc(v_fst_4768_);
lean_dec(v_a_4766_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4832_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v_visitedNames_4772_; lean_object* v_visitedLevels_4773_; lean_object* v_visitedExprs_4774_; lean_object* v_visitedConstants_4775_; lean_object* v_noMDataExprs_4776_; uint8_t v_exportMData_4777_; uint8_t v_exportUnsafe_4778_; uint8_t v_ignoreMissing_4779_; lean_object* v_recursorMap_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4831_; 
v_visitedNames_4772_ = lean_ctor_get(v_snd_4767_, 0);
v_visitedLevels_4773_ = lean_ctor_get(v_snd_4767_, 1);
v_visitedExprs_4774_ = lean_ctor_get(v_snd_4767_, 2);
v_visitedConstants_4775_ = lean_ctor_get(v_snd_4767_, 3);
v_noMDataExprs_4776_ = lean_ctor_get(v_snd_4767_, 4);
v_exportMData_4777_ = lean_ctor_get_uint8(v_snd_4767_, sizeof(void*)*6);
v_exportUnsafe_4778_ = lean_ctor_get_uint8(v_snd_4767_, sizeof(void*)*6 + 1);
v_ignoreMissing_4779_ = lean_ctor_get_uint8(v_snd_4767_, sizeof(void*)*6 + 2);
v_recursorMap_4780_ = lean_ctor_get(v_snd_4767_, 5);
v_isSharedCheck_4831_ = !lean_is_exclusive(v_snd_4767_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4782_ = v_snd_4767_;
v_isShared_4783_ = v_isSharedCheck_4831_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_recursorMap_4780_);
lean_inc(v_noMDataExprs_4776_);
lean_inc(v_visitedConstants_4775_);
lean_inc(v_visitedExprs_4774_);
lean_inc(v_visitedLevels_4773_);
lean_inc(v_visitedNames_4772_);
lean_dec(v_snd_4767_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4831_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v_type_4784_; lean_object* v___x_4785_; lean_object* v___x_4787_; 
v_type_4784_ = lean_ctor_get(v_toConstantVal_4761_, 2);
lean_inc_ref(v_type_4784_);
lean_dec_ref(v_toConstantVal_4761_);
lean_inc(v_head_4721_);
v___x_4785_ = l_Lean_NameHashSet_insert(v_visitedConstants_4775_, v_head_4721_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 3, v___x_4785_);
v___x_4787_ = v___x_4782_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_visitedNames_4772_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_visitedLevels_4773_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_visitedExprs_4774_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_noMDataExprs_4776_);
lean_ctor_set(v_reuseFailAlloc_4830_, 5, v_recursorMap_4780_);
lean_ctor_set_uint8(v_reuseFailAlloc_4830_, sizeof(void*)*6, v_exportMData_4777_);
lean_ctor_set_uint8(v_reuseFailAlloc_4830_, sizeof(void*)*6 + 1, v_exportUnsafe_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4830_, sizeof(void*)*6 + 2, v_ignoreMissing_4779_);
v___x_4787_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4788_; 
v___x_4788_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4784_, v___y_4716_, v___x_4787_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v_snd_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4820_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
lean_dec_ref_known(v___x_4788_, 1);
v_snd_4790_ = lean_ctor_get(v_a_4789_, 1);
v_isSharedCheck_4820_ = !lean_is_exclusive(v_a_4789_);
if (v_isSharedCheck_4820_ == 0)
{
lean_object* v_unused_4821_; 
v_unused_4821_ = lean_ctor_get(v_a_4789_, 0);
lean_dec(v_unused_4821_);
v___x_4792_ = v_a_4789_;
v_isShared_4793_ = v_isSharedCheck_4820_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_snd_4790_);
lean_dec(v_a_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4820_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v_toConstantVal_4794_; lean_object* v_recursorMap_4795_; lean_object* v_name_4796_; lean_object* v___x_4797_; 
v_toConstantVal_4794_ = lean_ctor_get(v_val_4713_, 0);
v_recursorMap_4795_ = lean_ctor_get(v_snd_4790_, 5);
v_name_4796_ = lean_ctor_get(v_toConstantVal_4794_, 0);
v___x_4797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4795_, v_name_4796_);
if (lean_obj_tag(v___x_4797_) == 1)
{
lean_object* v_val_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
v_val_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_val_4798_);
lean_dec_ref_known(v___x_4797_, 1);
v___x_4799_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4800_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4799_, v_snd_4758_, v_val_4798_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 1, v___x_4800_);
lean_ctor_set(v___x_4792_, 0, v_fst_4768_);
v___x_4802_ = v___x_4792_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_fst_4768_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; 
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 1, v___x_4802_);
lean_ctor_set(v___x_4770_, 0, v___x_4764_);
v___x_4804_ = v___x_4770_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
v_as_x27_4714_ = v_tail_4722_;
v_b_4715_ = v___x_4804_;
v___y_4717_ = v_snd_4790_;
goto _start;
}
}
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
lean_dec(v___x_4797_);
v___x_4808_ = lean_array_get_size(v_fst_4768_);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = lean_nat_dec_eq(v___x_4808_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
lean_del_object(v___x_4792_);
lean_del_object(v___x_4770_);
lean_dec(v_fst_4768_);
lean_dec_ref(v___x_4764_);
lean_dec(v_snd_4758_);
v___x_4811_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4812_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4811_, v___y_4716_, v_snd_4790_);
v___y_4724_ = v___x_4812_;
goto v___jp_4723_;
}
else
{
lean_object* v___x_4814_; 
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 1, v_snd_4758_);
lean_ctor_set(v___x_4792_, 0, v_fst_4768_);
v___x_4814_ = v___x_4792_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_fst_4768_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_snd_4758_);
v___x_4814_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
lean_object* v___x_4816_; 
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 1, v___x_4814_);
lean_ctor_set(v___x_4770_, 0, v___x_4764_);
v___x_4816_ = v___x_4770_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___x_4814_);
v___x_4816_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
v_as_x27_4714_ = v_tail_4722_;
v_b_4715_ = v___x_4816_;
v___y_4717_ = v_snd_4790_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_del_object(v___x_4770_);
lean_dec(v_fst_4768_);
lean_dec_ref(v___x_4764_);
lean_dec(v_snd_4758_);
v_a_4822_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4788_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4788_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec_ref(v___x_4764_);
lean_dec_ref(v_toConstantVal_4761_);
lean_dec(v_snd_4758_);
v_a_4833_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4765_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4765_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
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
v___jp_4841_:
{
lean_object* v___x_4843_; uint8_t v_isUnsafe_4844_; 
v___x_4843_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4842_);
lean_dec_ref(v___y_4842_);
v_isUnsafe_4844_ = lean_ctor_get_uint8(v___x_4843_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4844_ == 0)
{
lean_object* v_toConstantVal_4845_; lean_object* v_ctors_4846_; uint8_t v___x_4847_; 
v_toConstantVal_4845_ = lean_ctor_get(v___x_4843_, 0);
lean_inc_ref(v_toConstantVal_4845_);
v_ctors_4846_ = lean_ctor_get(v___x_4843_, 4);
lean_inc(v_ctors_4846_);
v___x_4847_ = 1;
v___y_4760_ = v___x_4843_;
v_toConstantVal_4761_ = v_toConstantVal_4845_;
v_ctors_4762_ = v_ctors_4846_;
v___y_4763_ = v___x_4847_;
goto v___jp_4759_;
}
else
{
uint8_t v_exportUnsafe_4848_; 
v_exportUnsafe_4848_ = lean_ctor_get_uint8(v___y_4717_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4848_ == 0)
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_dec_ref(v___x_4843_);
lean_dec(v_snd_4758_);
lean_dec(v_fst_4757_);
lean_dec(v_fst_4756_);
v___x_4849_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4850_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4849_, v___y_4716_, v___y_4717_);
v___y_4724_ = v___x_4850_;
goto v___jp_4723_;
}
else
{
lean_object* v_toConstantVal_4851_; lean_object* v_ctors_4852_; 
v_toConstantVal_4851_ = lean_ctor_get(v___x_4843_, 0);
lean_inc_ref(v_toConstantVal_4851_);
v_ctors_4852_ = lean_ctor_get(v___x_4843_, 4);
lean_inc(v_ctors_4852_);
v___y_4760_ = v___x_4843_;
v_toConstantVal_4761_ = v_toConstantVal_4851_;
v_ctors_4762_ = v_ctors_4852_;
v___y_4763_ = v_exportUnsafe_4848_;
goto v___jp_4759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object* v_as_4857_, size_t v_sz_4858_, size_t v_i_4859_, lean_object* v_b_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
uint8_t v___x_4864_; 
v___x_4864_ = lean_usize_dec_lt(v_i_4859_, v_sz_4858_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_b_4860_);
lean_ctor_set(v___x_4865_, 1, v___y_4862_);
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
else
{
lean_object* v_visitedNames_4867_; lean_object* v_visitedLevels_4868_; lean_object* v_visitedExprs_4869_; lean_object* v_visitedConstants_4870_; lean_object* v_noMDataExprs_4871_; uint8_t v_exportMData_4872_; uint8_t v_exportUnsafe_4873_; uint8_t v_ignoreMissing_4874_; lean_object* v_recursorMap_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4894_; 
v_visitedNames_4867_ = lean_ctor_get(v___y_4862_, 0);
v_visitedLevels_4868_ = lean_ctor_get(v___y_4862_, 1);
v_visitedExprs_4869_ = lean_ctor_get(v___y_4862_, 2);
v_visitedConstants_4870_ = lean_ctor_get(v___y_4862_, 3);
v_noMDataExprs_4871_ = lean_ctor_get(v___y_4862_, 4);
v_exportMData_4872_ = lean_ctor_get_uint8(v___y_4862_, sizeof(void*)*6);
v_exportUnsafe_4873_ = lean_ctor_get_uint8(v___y_4862_, sizeof(void*)*6 + 1);
v_ignoreMissing_4874_ = lean_ctor_get_uint8(v___y_4862_, sizeof(void*)*6 + 2);
v_recursorMap_4875_ = lean_ctor_get(v___y_4862_, 5);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___y_4862_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4877_ = v___y_4862_;
v_isShared_4878_ = v_isSharedCheck_4894_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_recursorMap_4875_);
lean_inc(v_noMDataExprs_4871_);
lean_inc(v_visitedConstants_4870_);
lean_inc(v_visitedExprs_4869_);
lean_inc(v_visitedLevels_4868_);
lean_inc(v_visitedNames_4867_);
lean_dec(v___y_4862_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4894_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v_a_4879_; lean_object* v_toConstantVal_4880_; lean_object* v_name_4881_; lean_object* v_type_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v_a_4879_ = lean_array_uget_borrowed(v_as_4857_, v_i_4859_);
v_toConstantVal_4880_ = lean_ctor_get(v_a_4879_, 0);
v_name_4881_ = lean_ctor_get(v_toConstantVal_4880_, 0);
v_type_4882_ = lean_ctor_get(v_toConstantVal_4880_, 2);
v___x_4883_ = lean_box(0);
lean_inc(v_name_4881_);
v___x_4884_ = l_Lean_NameHashSet_insert(v_visitedConstants_4870_, v_name_4881_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 3, v___x_4884_);
v___x_4886_ = v___x_4877_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_visitedNames_4867_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v_visitedLevels_4868_);
lean_ctor_set(v_reuseFailAlloc_4893_, 2, v_visitedExprs_4869_);
lean_ctor_set(v_reuseFailAlloc_4893_, 3, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4893_, 4, v_noMDataExprs_4871_);
lean_ctor_set(v_reuseFailAlloc_4893_, 5, v_recursorMap_4875_);
lean_ctor_set_uint8(v_reuseFailAlloc_4893_, sizeof(void*)*6, v_exportMData_4872_);
lean_ctor_set_uint8(v_reuseFailAlloc_4893_, sizeof(void*)*6 + 1, v_exportUnsafe_4873_);
lean_ctor_set_uint8(v_reuseFailAlloc_4893_, sizeof(void*)*6 + 2, v_ignoreMissing_4874_);
v___x_4886_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
lean_object* v___x_4887_; 
lean_inc_ref(v_type_4882_);
v___x_4887_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4882_, v___y_4861_, v___x_4886_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v_snd_4889_; size_t v___x_4890_; size_t v___x_4891_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v_snd_4889_ = lean_ctor_get(v_a_4888_, 1);
lean_inc(v_snd_4889_);
lean_dec(v_a_4888_);
v___x_4890_ = ((size_t)1ULL);
v___x_4891_ = lean_usize_add(v_i_4859_, v___x_4890_);
v_i_4859_ = v___x_4891_;
v_b_4860_ = v___x_4883_;
v___y_4862_ = v_snd_4889_;
goto _start;
}
else
{
return v___x_4887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4895_, lean_object* v_b_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
if (lean_obj_tag(v_as_x27_4895_) == 0)
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v_b_4896_);
lean_ctor_set(v___x_4900_, 1, v___y_4898_);
v___x_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
return v___x_4901_;
}
else
{
lean_object* v_head_4902_; lean_object* v_tail_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v_head_4902_ = lean_ctor_get(v_as_x27_4895_, 0);
v_tail_4903_ = lean_ctor_get(v_as_x27_4895_, 1);
v___x_4904_ = lean_box(0);
lean_inc(v_head_4902_);
v___x_4905_ = l_LeanExport_dumpConstant(v_head_4902_, v___y_4897_, v___y_4898_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v_snd_4907_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_a_4906_);
lean_dec_ref_known(v___x_4905_, 1);
v_snd_4907_ = lean_ctor_get(v_a_4906_, 1);
lean_inc(v_snd_4907_);
lean_dec(v_a_4906_);
v_as_x27_4895_ = v_tail_4903_;
v_b_4896_ = v___x_4904_;
v___y_4898_ = v_snd_4907_;
goto _start;
}
else
{
return v___x_4905_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v_fst_4921_; lean_object* v_snd_4922_; uint8_t v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = 0;
lean_inc(v_c_4909_);
lean_inc_ref(v_a_4910_);
v___x_5020_ = l_Lean_Environment_find_x3f(v_a_4910_, v_c_4909_, v___x_5019_);
if (lean_obj_tag(v___x_5020_) == 1)
{
lean_object* v_val_5021_; uint8_t v___x_5759_; 
v_val_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_val_5021_);
lean_dec_ref_known(v___x_5020_, 1);
v___x_5759_ = l_Lean_ConstantInfo_isUnsafe(v_val_5021_);
if (v___x_5759_ == 0)
{
goto v___jp_5022_;
}
else
{
uint8_t v_exportUnsafe_5760_; 
v_exportUnsafe_5760_ = lean_ctor_get_uint8(v_a_4911_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5760_ == 0)
{
lean_dec(v_val_5021_);
lean_dec(v_c_4909_);
goto v___jp_4913_;
}
else
{
goto v___jp_5022_;
}
}
v___jp_5022_:
{
lean_object* v_visitedNames_5023_; lean_object* v_visitedLevels_5024_; lean_object* v_visitedExprs_5025_; lean_object* v_visitedConstants_5026_; lean_object* v_noMDataExprs_5027_; uint8_t v_exportMData_5028_; uint8_t v_exportUnsafe_5029_; uint8_t v_ignoreMissing_5030_; lean_object* v_recursorMap_5031_; uint8_t v___x_5032_; 
v_visitedNames_5023_ = lean_ctor_get(v_a_4911_, 0);
v_visitedLevels_5024_ = lean_ctor_get(v_a_4911_, 1);
v_visitedExprs_5025_ = lean_ctor_get(v_a_4911_, 2);
v_visitedConstants_5026_ = lean_ctor_get(v_a_4911_, 3);
v_noMDataExprs_5027_ = lean_ctor_get(v_a_4911_, 4);
v_exportMData_5028_ = lean_ctor_get_uint8(v_a_4911_, sizeof(void*)*6);
v_exportUnsafe_5029_ = lean_ctor_get_uint8(v_a_4911_, sizeof(void*)*6 + 1);
v_ignoreMissing_5030_ = lean_ctor_get_uint8(v_a_4911_, sizeof(void*)*6 + 2);
v_recursorMap_5031_ = lean_ctor_get(v_a_4911_, 5);
v___x_5032_ = l_Lean_NameHashSet_contains(v_visitedConstants_5026_, v_c_4909_);
if (v___x_5032_ == 0)
{
lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5752_; 
lean_inc(v_recursorMap_5031_);
lean_inc_ref(v_noMDataExprs_5027_);
lean_inc_ref(v_visitedConstants_5026_);
lean_inc_ref(v_visitedExprs_5025_);
lean_inc_ref(v_visitedLevels_5024_);
lean_inc_ref(v_visitedNames_5023_);
v_isSharedCheck_5752_ = !lean_is_exclusive(v_a_4911_);
if (v_isSharedCheck_5752_ == 0)
{
lean_object* v_unused_5753_; lean_object* v_unused_5754_; lean_object* v_unused_5755_; lean_object* v_unused_5756_; lean_object* v_unused_5757_; lean_object* v_unused_5758_; 
v_unused_5753_ = lean_ctor_get(v_a_4911_, 5);
lean_dec(v_unused_5753_);
v_unused_5754_ = lean_ctor_get(v_a_4911_, 4);
lean_dec(v_unused_5754_);
v_unused_5755_ = lean_ctor_get(v_a_4911_, 3);
lean_dec(v_unused_5755_);
v_unused_5756_ = lean_ctor_get(v_a_4911_, 2);
lean_dec(v_unused_5756_);
v_unused_5757_ = lean_ctor_get(v_a_4911_, 1);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_a_4911_, 0);
lean_dec(v_unused_5758_);
v___x_5034_ = v_a_4911_;
v_isShared_5035_ = v_isSharedCheck_5752_;
goto v_resetjp_5033_;
}
else
{
lean_dec(v_a_4911_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5752_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; lean_object* v___x_5038_; 
v___x_5036_ = l_Lean_NameHashSet_insert(v_visitedConstants_5026_, v_c_4909_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 3, v___x_5036_);
v___x_5038_ = v___x_5034_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_visitedNames_5023_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v_visitedLevels_5024_);
lean_ctor_set(v_reuseFailAlloc_5751_, 2, v_visitedExprs_5025_);
lean_ctor_set(v_reuseFailAlloc_5751_, 3, v___x_5036_);
lean_ctor_set(v_reuseFailAlloc_5751_, 4, v_noMDataExprs_5027_);
lean_ctor_set(v_reuseFailAlloc_5751_, 5, v_recursorMap_5031_);
lean_ctor_set_uint8(v_reuseFailAlloc_5751_, sizeof(void*)*6, v_exportMData_5028_);
lean_ctor_set_uint8(v_reuseFailAlloc_5751_, sizeof(void*)*6 + 1, v_exportUnsafe_5029_);
lean_ctor_set_uint8(v_reuseFailAlloc_5751_, sizeof(void*)*6 + 2, v_ignoreMissing_5030_);
v___x_5038_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
switch(lean_obj_tag(v_val_5021_))
{
case 0:
{
lean_object* v_val_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5143_; 
v_val_5039_ = lean_ctor_get(v_val_5021_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v_val_5021_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5041_ = v_val_5021_;
v_isShared_5042_ = v_isSharedCheck_5143_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_val_5039_);
lean_dec(v_val_5021_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5143_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v_toConstantVal_5043_; uint8_t v_isUnsafe_5044_; lean_object* v_name_5045_; lean_object* v_levelParams_5046_; lean_object* v_type_5047_; lean_object* v___x_5048_; 
v_toConstantVal_5043_ = lean_ctor_get(v_val_5039_, 0);
lean_inc_ref(v_toConstantVal_5043_);
v_isUnsafe_5044_ = lean_ctor_get_uint8(v_val_5039_, sizeof(void*)*1);
lean_dec_ref(v_val_5039_);
v_name_5045_ = lean_ctor_get(v_toConstantVal_5043_, 0);
lean_inc(v_name_5045_);
v_levelParams_5046_ = lean_ctor_get(v_toConstantVal_5043_, 1);
lean_inc(v_levelParams_5046_);
v_type_5047_ = lean_ctor_get(v_toConstantVal_5043_, 2);
lean_inc_ref_n(v_type_5047_, 2);
lean_dec_ref(v_toConstantVal_5043_);
v___x_5048_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5047_, v_a_4910_, v___x_5038_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5142_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5051_ = v___x_5048_;
v_isShared_5052_ = v_isSharedCheck_5142_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_5048_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5142_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v_snd_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5140_; 
v_snd_5053_ = lean_ctor_get(v_a_5049_, 1);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_a_5049_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; 
v_unused_5141_ = lean_ctor_get(v_a_5049_, 0);
lean_dec(v_unused_5141_);
v___x_5055_ = v_a_5049_;
v_isShared_5056_ = v_isSharedCheck_5140_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_snd_5053_);
lean_dec(v_a_5049_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5140_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; 
v___x_5057_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5045_, v_a_4910_, v_snd_5053_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v_fst_5059_; lean_object* v_snd_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5131_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v_fst_5059_ = lean_ctor_get(v_a_5058_, 0);
v_snd_5060_ = lean_ctor_get(v_a_5058_, 1);
v_isSharedCheck_5131_ = !lean_is_exclusive(v_a_5058_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5062_ = v_a_5058_;
v_isShared_5063_ = v_isSharedCheck_5131_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_snd_5060_);
lean_inc(v_fst_5059_);
lean_dec(v_a_5058_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5131_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5064_; 
v___x_5064_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5046_, v_a_4910_, v_snd_5060_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; lean_object* v_fst_5066_; lean_object* v_snd_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5122_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___x_5064_, 1);
v_fst_5066_ = lean_ctor_get(v_a_5065_, 0);
v_snd_5067_ = lean_ctor_get(v_a_5065_, 1);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_a_5065_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5069_ = v_a_5065_;
v_isShared_5070_ = v_isSharedCheck_5122_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_snd_5067_);
lean_inc(v_fst_5066_);
lean_dec(v_a_5065_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5122_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; 
v___x_5071_ = l_LeanExport_dumpExpr(v_type_5047_, v_a_4910_, v_snd_5067_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v_a_5072_; lean_object* v_fst_5073_; lean_object* v_snd_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5113_; 
v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_5071_, 1);
v_fst_5073_ = lean_ctor_get(v_a_5072_, 0);
v_snd_5074_ = lean_ctor_get(v_a_5072_, 1);
v_isSharedCheck_5113_ = !lean_is_exclusive(v_a_5072_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5076_ = v_a_5072_;
v_isShared_5077_ = v_isSharedCheck_5113_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_snd_5074_);
lean_inc(v_fst_5073_);
lean_dec(v_a_5072_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5113_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___x_5078_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_5079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5080_ = l_Lean_JsonNumber_fromNat(v_fst_5059_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set_tag(v___x_5051_, 2);
lean_ctor_set(v___x_5051_, 0, v___x_5080_);
v___x_5082_ = v___x_5051_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___x_5084_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v___x_5082_);
lean_ctor_set(v___x_5076_, 0, v___x_5079_);
v___x_5084_ = v___x_5076_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5079_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 1, v_fst_5066_);
lean_ctor_set(v___x_5069_, 0, v___x_5085_);
v___x_5087_ = v___x_5069_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5085_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_fst_5066_);
v___x_5087_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5088_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5089_ = l_Lean_JsonNumber_fromNat(v_fst_5073_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set_tag(v___x_5041_, 2);
lean_ctor_set(v___x_5041_, 0, v___x_5089_);
v___x_5091_ = v___x_5041_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
lean_object* v___x_5093_; 
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 1, v___x_5091_);
lean_ctor_set(v___x_5062_, 0, v___x_5088_);
v___x_5093_ = v___x_5062_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5088_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___x_5091_);
v___x_5093_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5097_; 
v___x_5094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_5095_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5095_, 0, v_isUnsafe_5044_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 1, v___x_5095_);
lean_ctor_set(v___x_5055_, 0, v___x_5094_);
v___x_5097_ = v___x_5055_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5107_, 1, v___x_5095_);
v___x_5097_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5098_ = lean_box(0);
v___x_5099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5093_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
v___x_5101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5087_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5084_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
v___x_5103_ = l_Lean_Json_mkObj(v___x_5102_);
lean_dec_ref_known(v___x_5102_, 2);
v___x_5104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5078_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
lean_ctor_set(v___x_5105_, 1, v___x_5098_);
v___x_5106_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5105_, v_snd_5074_);
lean_dec_ref_known(v___x_5105_, 2);
return v___x_5106_;
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
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_del_object(v___x_5069_);
lean_dec(v_fst_5066_);
lean_del_object(v___x_5062_);
lean_dec(v_fst_5059_);
lean_del_object(v___x_5055_);
lean_del_object(v___x_5051_);
lean_del_object(v___x_5041_);
v_a_5114_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5071_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5071_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
lean_del_object(v___x_5062_);
lean_dec(v_fst_5059_);
lean_del_object(v___x_5055_);
lean_del_object(v___x_5051_);
lean_dec_ref(v_type_5047_);
lean_del_object(v___x_5041_);
v_a_5123_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5064_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5064_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_del_object(v___x_5055_);
lean_del_object(v___x_5051_);
lean_dec_ref(v_type_5047_);
lean_dec(v_levelParams_5046_);
lean_del_object(v___x_5041_);
v_a_5132_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5057_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5057_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_dec_ref(v_type_5047_);
lean_dec(v_levelParams_5046_);
lean_dec(v_name_5045_);
lean_del_object(v___x_5041_);
return v___x_5048_;
}
}
}
case 1:
{
lean_object* v_val_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5315_; 
v_val_5144_ = lean_ctor_get(v_val_5021_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v_val_5021_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5146_ = v_val_5021_;
v_isShared_5147_ = v_isSharedCheck_5315_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_val_5144_);
lean_dec(v_val_5021_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5315_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v_toConstantVal_5148_; lean_object* v_value_5149_; lean_object* v_hints_5150_; uint8_t v_safety_5151_; lean_object* v_all_5152_; lean_object* v_name_5153_; lean_object* v_levelParams_5154_; lean_object* v_type_5155_; lean_object* v___x_5156_; 
v_toConstantVal_5148_ = lean_ctor_get(v_val_5144_, 0);
lean_inc_ref(v_toConstantVal_5148_);
v_value_5149_ = lean_ctor_get(v_val_5144_, 1);
lean_inc_ref(v_value_5149_);
v_hints_5150_ = lean_ctor_get(v_val_5144_, 2);
lean_inc(v_hints_5150_);
v_safety_5151_ = lean_ctor_get_uint8(v_val_5144_, sizeof(void*)*4);
v_all_5152_ = lean_ctor_get(v_val_5144_, 3);
lean_inc(v_all_5152_);
lean_dec_ref(v_val_5144_);
v_name_5153_ = lean_ctor_get(v_toConstantVal_5148_, 0);
lean_inc(v_name_5153_);
v_levelParams_5154_ = lean_ctor_get(v_toConstantVal_5148_, 1);
lean_inc(v_levelParams_5154_);
v_type_5155_ = lean_ctor_get(v_toConstantVal_5148_, 2);
lean_inc_ref_n(v_type_5155_, 2);
lean_dec_ref(v_toConstantVal_5148_);
v___x_5156_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5155_, v_a_4910_, v___x_5038_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5314_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5159_ = v___x_5156_;
v_isShared_5160_ = v_isSharedCheck_5314_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5156_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5314_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v_snd_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5312_; 
v_snd_5161_ = lean_ctor_get(v_a_5157_, 1);
v_isSharedCheck_5312_ = !lean_is_exclusive(v_a_5157_);
if (v_isSharedCheck_5312_ == 0)
{
lean_object* v_unused_5313_; 
v_unused_5313_ = lean_ctor_get(v_a_5157_, 0);
lean_dec(v_unused_5313_);
v___x_5163_ = v_a_5157_;
v_isShared_5164_ = v_isSharedCheck_5312_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_snd_5161_);
lean_dec(v_a_5157_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5312_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5165_; 
lean_inc_ref(v_value_5149_);
v___x_5165_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5149_, v_a_4910_, v_snd_5161_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5311_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5168_ = v___x_5165_;
v_isShared_5169_ = v_isSharedCheck_5311_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5165_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5311_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v_snd_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5309_; 
v_snd_5170_ = lean_ctor_get(v_a_5166_, 1);
v_isSharedCheck_5309_ = !lean_is_exclusive(v_a_5166_);
if (v_isSharedCheck_5309_ == 0)
{
lean_object* v_unused_5310_; 
v_unused_5310_ = lean_ctor_get(v_a_5166_, 0);
lean_dec(v_unused_5310_);
v___x_5172_ = v_a_5166_;
v_isShared_5173_ = v_isSharedCheck_5309_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_snd_5170_);
lean_dec(v_a_5166_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5309_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5174_; 
v___x_5174_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5153_, v_a_4910_, v_snd_5170_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v_fst_5176_; lean_object* v_snd_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5300_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5174_, 1);
v_fst_5176_ = lean_ctor_get(v_a_5175_, 0);
v_snd_5177_ = lean_ctor_get(v_a_5175_, 1);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_a_5175_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5179_ = v_a_5175_;
v_isShared_5180_ = v_isSharedCheck_5300_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_snd_5177_);
lean_inc(v_fst_5176_);
lean_dec(v_a_5175_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5300_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5181_; 
v___x_5181_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5154_, v_a_4910_, v_snd_5177_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; lean_object* v_fst_5183_; lean_object* v_snd_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5291_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5181_, 1);
v_fst_5183_ = lean_ctor_get(v_a_5182_, 0);
v_snd_5184_ = lean_ctor_get(v_a_5182_, 1);
v_isSharedCheck_5291_ = !lean_is_exclusive(v_a_5182_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5186_ = v_a_5182_;
v_isShared_5187_ = v_isSharedCheck_5291_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_snd_5184_);
lean_inc(v_fst_5183_);
lean_dec(v_a_5182_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5291_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5188_; 
v___x_5188_ = l_LeanExport_dumpExpr(v_type_5155_, v_a_4910_, v_snd_5184_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v_fst_5190_; lean_object* v_snd_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5282_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5188_, 1);
v_fst_5190_ = lean_ctor_get(v_a_5189_, 0);
v_snd_5191_ = lean_ctor_get(v_a_5189_, 1);
v_isSharedCheck_5282_ = !lean_is_exclusive(v_a_5189_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5193_ = v_a_5189_;
v_isShared_5194_ = v_isSharedCheck_5282_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_snd_5191_);
lean_inc(v_fst_5190_);
lean_dec(v_a_5189_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5282_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5195_; 
v___x_5195_ = l_LeanExport_dumpExpr(v_value_5149_, v_a_4910_, v_snd_5191_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; lean_object* v_fst_5197_; lean_object* v_snd_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5273_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v_fst_5197_ = lean_ctor_get(v_a_5196_, 0);
v_snd_5198_ = lean_ctor_get(v_a_5196_, 1);
v_isSharedCheck_5273_ = !lean_is_exclusive(v_a_5196_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5200_ = v_a_5196_;
v_isShared_5201_ = v_isSharedCheck_5273_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_snd_5198_);
lean_inc(v_fst_5197_);
lean_dec(v_a_5196_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5273_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5202_; 
v___x_5202_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5152_, v_a_4910_, v_snd_5198_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; lean_object* v_fst_5204_; lean_object* v_snd_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5264_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
lean_inc(v_a_5203_);
lean_dec_ref_known(v___x_5202_, 1);
v_fst_5204_ = lean_ctor_get(v_a_5203_, 0);
v_snd_5205_ = lean_ctor_get(v_a_5203_, 1);
v_isSharedCheck_5264_ = !lean_is_exclusive(v_a_5203_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5207_ = v_a_5203_;
v_isShared_5208_ = v_isSharedCheck_5264_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_snd_5205_);
lean_inc(v_fst_5204_);
lean_dec(v_a_5203_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5264_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5213_; 
v___x_5209_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_5210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5211_ = l_Lean_JsonNumber_fromNat(v_fst_5176_);
if (v_isShared_5169_ == 0)
{
lean_ctor_set_tag(v___x_5168_, 2);
lean_ctor_set(v___x_5168_, 0, v___x_5211_);
v___x_5213_ = v___x_5168_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5211_);
v___x_5213_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
lean_object* v___x_5215_; 
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 1, v___x_5213_);
lean_ctor_set(v___x_5207_, 0, v___x_5210_);
v___x_5215_ = v___x_5207_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5210_);
lean_ctor_set(v_reuseFailAlloc_5262_, 1, v___x_5213_);
v___x_5215_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5201_ == 0)
{
lean_ctor_set(v___x_5200_, 1, v_fst_5183_);
lean_ctor_set(v___x_5200_, 0, v___x_5216_);
v___x_5218_ = v___x_5200_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5261_, 1, v_fst_5183_);
v___x_5218_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5219_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5220_ = l_Lean_JsonNumber_fromNat(v_fst_5190_);
if (v_isShared_5160_ == 0)
{
lean_ctor_set_tag(v___x_5159_, 2);
lean_ctor_set(v___x_5159_, 0, v___x_5220_);
v___x_5222_ = v___x_5159_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5220_);
v___x_5222_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5224_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 1, v___x_5222_);
lean_ctor_set(v___x_5193_, 0, v___x_5219_);
v___x_5224_ = v___x_5193_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5219_);
lean_ctor_set(v_reuseFailAlloc_5259_, 1, v___x_5222_);
v___x_5224_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5228_; 
v___x_5225_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5226_ = l_Lean_JsonNumber_fromNat(v_fst_5197_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set_tag(v___x_5146_, 2);
lean_ctor_set(v___x_5146_, 0, v___x_5226_);
v___x_5228_ = v___x_5146_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5226_);
v___x_5228_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
lean_object* v___x_5230_; 
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 1, v___x_5228_);
lean_ctor_set(v___x_5186_, 0, v___x_5225_);
v___x_5230_ = v___x_5186_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5225_);
lean_ctor_set(v_reuseFailAlloc_5257_, 1, v___x_5228_);
v___x_5230_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5234_; 
v___x_5231_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_5232_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_5150_);
lean_dec(v_hints_5150_);
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 1, v___x_5232_);
lean_ctor_set(v___x_5179_, 0, v___x_5231_);
v___x_5234_ = v___x_5179_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5231_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v___x_5232_);
v___x_5234_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5238_; 
v___x_5235_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_5236_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_5151_);
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 1, v___x_5236_);
lean_ctor_set(v___x_5172_, 0, v___x_5235_);
v___x_5238_ = v___x_5172_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5235_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
v___x_5239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 1, v_fst_5204_);
lean_ctor_set(v___x_5163_, 0, v___x_5239_);
v___x_5241_ = v___x_5163_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5239_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_fst_5204_);
v___x_5241_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5242_ = lean_box(0);
v___x_5243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5241_);
lean_ctor_set(v___x_5243_, 1, v___x_5242_);
v___x_5244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5238_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5234_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5230_);
lean_ctor_set(v___x_5246_, 1, v___x_5245_);
v___x_5247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5224_);
lean_ctor_set(v___x_5247_, 1, v___x_5246_);
v___x_5248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5218_);
lean_ctor_set(v___x_5248_, 1, v___x_5247_);
v___x_5249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5215_);
lean_ctor_set(v___x_5249_, 1, v___x_5248_);
v___x_5250_ = l_Lean_Json_mkObj(v___x_5249_);
lean_dec_ref_known(v___x_5249_, 2);
v___x_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5209_);
lean_ctor_set(v___x_5251_, 1, v___x_5250_);
v___x_5252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
lean_ctor_set(v___x_5252_, 1, v___x_5242_);
v___x_5253_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5252_, v_snd_5205_);
lean_dec_ref_known(v___x_5252_, 2);
return v___x_5253_;
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
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5272_; 
lean_del_object(v___x_5200_);
lean_dec(v_fst_5197_);
lean_del_object(v___x_5193_);
lean_dec(v_fst_5190_);
lean_del_object(v___x_5186_);
lean_dec(v_fst_5183_);
lean_del_object(v___x_5179_);
lean_dec(v_fst_5176_);
lean_del_object(v___x_5172_);
lean_del_object(v___x_5168_);
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec(v_hints_5150_);
lean_del_object(v___x_5146_);
v_a_5265_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5267_ = v___x_5202_;
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5202_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_del_object(v___x_5193_);
lean_dec(v_fst_5190_);
lean_del_object(v___x_5186_);
lean_dec(v_fst_5183_);
lean_del_object(v___x_5179_);
lean_dec(v_fst_5176_);
lean_del_object(v___x_5172_);
lean_del_object(v___x_5168_);
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_del_object(v___x_5146_);
v_a_5274_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5195_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5195_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
else
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5290_; 
lean_del_object(v___x_5186_);
lean_dec(v_fst_5183_);
lean_del_object(v___x_5179_);
lean_dec(v_fst_5176_);
lean_del_object(v___x_5172_);
lean_del_object(v___x_5168_);
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_dec_ref(v_value_5149_);
lean_del_object(v___x_5146_);
v_a_5283_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5285_ = v___x_5188_;
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5188_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5286_ == 0)
{
v___x_5288_ = v___x_5285_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_a_5283_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
}
else
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5299_; 
lean_del_object(v___x_5179_);
lean_dec(v_fst_5176_);
lean_del_object(v___x_5172_);
lean_del_object(v___x_5168_);
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec_ref(v_type_5155_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_dec_ref(v_value_5149_);
lean_del_object(v___x_5146_);
v_a_5292_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5294_ = v___x_5181_;
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5181_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5297_; 
if (v_isShared_5295_ == 0)
{
v___x_5297_ = v___x_5294_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_del_object(v___x_5172_);
lean_del_object(v___x_5168_);
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec_ref(v_type_5155_);
lean_dec(v_levelParams_5154_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_dec_ref(v_value_5149_);
lean_del_object(v___x_5146_);
v_a_5301_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5174_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5174_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5163_);
lean_del_object(v___x_5159_);
lean_dec_ref(v_type_5155_);
lean_dec(v_levelParams_5154_);
lean_dec(v_name_5153_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_dec_ref(v_value_5149_);
lean_del_object(v___x_5146_);
return v___x_5165_;
}
}
}
}
else
{
lean_dec_ref(v_type_5155_);
lean_dec(v_levelParams_5154_);
lean_dec(v_name_5153_);
lean_dec(v_all_5152_);
lean_dec(v_hints_5150_);
lean_dec_ref(v_value_5149_);
lean_del_object(v___x_5146_);
return v___x_5156_;
}
}
}
case 2:
{
lean_object* v_val_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5477_; 
v_val_5316_ = lean_ctor_get(v_val_5021_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v_val_5021_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5318_ = v_val_5021_;
v_isShared_5319_ = v_isSharedCheck_5477_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_val_5316_);
lean_dec(v_val_5021_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5477_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v_toConstantVal_5320_; lean_object* v_value_5321_; lean_object* v_all_5322_; lean_object* v_name_5323_; lean_object* v_levelParams_5324_; lean_object* v_type_5325_; lean_object* v___x_5326_; 
v_toConstantVal_5320_ = lean_ctor_get(v_val_5316_, 0);
lean_inc_ref(v_toConstantVal_5320_);
v_value_5321_ = lean_ctor_get(v_val_5316_, 1);
lean_inc_ref(v_value_5321_);
v_all_5322_ = lean_ctor_get(v_val_5316_, 2);
lean_inc(v_all_5322_);
lean_dec_ref(v_val_5316_);
v_name_5323_ = lean_ctor_get(v_toConstantVal_5320_, 0);
lean_inc(v_name_5323_);
v_levelParams_5324_ = lean_ctor_get(v_toConstantVal_5320_, 1);
lean_inc(v_levelParams_5324_);
v_type_5325_ = lean_ctor_get(v_toConstantVal_5320_, 2);
lean_inc_ref_n(v_type_5325_, 2);
lean_dec_ref(v_toConstantVal_5320_);
v___x_5326_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5325_, v_a_4910_, v___x_5038_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5476_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5476_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5476_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v_snd_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5474_; 
v_snd_5331_ = lean_ctor_get(v_a_5327_, 1);
v_isSharedCheck_5474_ = !lean_is_exclusive(v_a_5327_);
if (v_isSharedCheck_5474_ == 0)
{
lean_object* v_unused_5475_; 
v_unused_5475_ = lean_ctor_get(v_a_5327_, 0);
lean_dec(v_unused_5475_);
v___x_5333_ = v_a_5327_;
v_isShared_5334_ = v_isSharedCheck_5474_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_snd_5331_);
lean_dec(v_a_5327_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5474_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5335_; 
lean_inc_ref(v_value_5321_);
v___x_5335_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5321_, v_a_4910_, v_snd_5331_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5473_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5473_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5473_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v_snd_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5471_; 
v_snd_5340_ = lean_ctor_get(v_a_5336_, 1);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_a_5336_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; 
v_unused_5472_ = lean_ctor_get(v_a_5336_, 0);
lean_dec(v_unused_5472_);
v___x_5342_ = v_a_5336_;
v_isShared_5343_ = v_isSharedCheck_5471_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_snd_5340_);
lean_dec(v_a_5336_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5471_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5344_; 
v___x_5344_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5323_, v_a_4910_, v_snd_5340_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v_fst_5346_; lean_object* v_snd_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5462_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc(v_a_5345_);
lean_dec_ref_known(v___x_5344_, 1);
v_fst_5346_ = lean_ctor_get(v_a_5345_, 0);
v_snd_5347_ = lean_ctor_get(v_a_5345_, 1);
v_isSharedCheck_5462_ = !lean_is_exclusive(v_a_5345_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5349_ = v_a_5345_;
v_isShared_5350_ = v_isSharedCheck_5462_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_snd_5347_);
lean_inc(v_fst_5346_);
lean_dec(v_a_5345_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5462_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5351_; 
v___x_5351_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5324_, v_a_4910_, v_snd_5347_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v_a_5352_; lean_object* v_fst_5353_; lean_object* v_snd_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5453_; 
v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc(v_a_5352_);
lean_dec_ref_known(v___x_5351_, 1);
v_fst_5353_ = lean_ctor_get(v_a_5352_, 0);
v_snd_5354_ = lean_ctor_get(v_a_5352_, 1);
v_isSharedCheck_5453_ = !lean_is_exclusive(v_a_5352_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5356_ = v_a_5352_;
v_isShared_5357_ = v_isSharedCheck_5453_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_snd_5354_);
lean_inc(v_fst_5353_);
lean_dec(v_a_5352_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5453_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5358_; 
v___x_5358_ = l_LeanExport_dumpExpr(v_type_5325_, v_a_4910_, v_snd_5354_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v_fst_5360_; lean_object* v_snd_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5444_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref_known(v___x_5358_, 1);
v_fst_5360_ = lean_ctor_get(v_a_5359_, 0);
v_snd_5361_ = lean_ctor_get(v_a_5359_, 1);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_a_5359_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5363_ = v_a_5359_;
v_isShared_5364_ = v_isSharedCheck_5444_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_snd_5361_);
lean_inc(v_fst_5360_);
lean_dec(v_a_5359_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5444_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_LeanExport_dumpExpr(v_value_5321_, v_a_4910_, v_snd_5361_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v_fst_5367_; lean_object* v_snd_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5435_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
lean_dec_ref_known(v___x_5365_, 1);
v_fst_5367_ = lean_ctor_get(v_a_5366_, 0);
v_snd_5368_ = lean_ctor_get(v_a_5366_, 1);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_a_5366_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5370_ = v_a_5366_;
v_isShared_5371_ = v_isSharedCheck_5435_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_snd_5368_);
lean_inc(v_fst_5367_);
lean_dec(v_a_5366_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5435_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5372_; 
v___x_5372_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5322_, v_a_4910_, v_snd_5368_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v_fst_5374_; lean_object* v_snd_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5426_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5372_, 1);
v_fst_5374_ = lean_ctor_get(v_a_5373_, 0);
v_snd_5375_ = lean_ctor_get(v_a_5373_, 1);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_a_5373_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5377_ = v_a_5373_;
v_isShared_5378_ = v_isSharedCheck_5426_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_snd_5375_);
lean_inc(v_fst_5374_);
lean_dec(v_a_5373_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5426_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5379_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5381_ = l_Lean_JsonNumber_fromNat(v_fst_5346_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set_tag(v___x_5338_, 2);
lean_ctor_set(v___x_5338_, 0, v___x_5381_);
v___x_5383_ = v___x_5338_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5381_);
v___x_5383_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
lean_object* v___x_5385_; 
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5383_);
lean_ctor_set(v___x_5377_, 0, v___x_5380_);
v___x_5385_ = v___x_5377_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v___x_5383_);
v___x_5385_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
lean_object* v___x_5386_; lean_object* v___x_5388_; 
v___x_5386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 1, v_fst_5353_);
lean_ctor_set(v___x_5370_, 0, v___x_5386_);
v___x_5388_ = v___x_5370_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_fst_5353_);
v___x_5388_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5389_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5390_ = l_Lean_JsonNumber_fromNat(v_fst_5360_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set_tag(v___x_5329_, 2);
lean_ctor_set(v___x_5329_, 0, v___x_5390_);
v___x_5392_ = v___x_5329_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5390_);
v___x_5392_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 1, v___x_5392_);
lean_ctor_set(v___x_5363_, 0, v___x_5389_);
v___x_5394_ = v___x_5363_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5389_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v___x_5392_);
v___x_5394_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5395_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5396_ = l_Lean_JsonNumber_fromNat(v_fst_5367_);
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 0, v___x_5396_);
v___x_5398_ = v___x_5318_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
lean_object* v___x_5400_; 
if (v_isShared_5357_ == 0)
{
lean_ctor_set(v___x_5356_, 1, v___x_5398_);
lean_ctor_set(v___x_5356_, 0, v___x_5395_);
v___x_5400_ = v___x_5356_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5395_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v_fst_5374_);
lean_ctor_set(v___x_5349_, 0, v___x_5401_);
v___x_5403_ = v___x_5349_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5401_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_fst_5374_);
v___x_5403_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5404_ = lean_box(0);
if (v_isShared_5334_ == 0)
{
lean_ctor_set_tag(v___x_5333_, 1);
lean_ctor_set(v___x_5333_, 1, v___x_5404_);
lean_ctor_set(v___x_5333_, 0, v___x_5403_);
v___x_5406_ = v___x_5333_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5403_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5413_; 
v___x_5407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5400_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
v___x_5408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5394_);
lean_ctor_set(v___x_5408_, 1, v___x_5407_);
v___x_5409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5388_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5385_);
lean_ctor_set(v___x_5410_, 1, v___x_5409_);
v___x_5411_ = l_Lean_Json_mkObj(v___x_5410_);
lean_dec_ref_known(v___x_5410_, 2);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 1, v___x_5411_);
lean_ctor_set(v___x_5342_, 0, v___x_5379_);
v___x_5413_ = v___x_5342_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5379_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
lean_ctor_set(v___x_5414_, 1, v___x_5404_);
v___x_5415_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5414_, v_snd_5375_);
lean_dec_ref_known(v___x_5414_, 2);
return v___x_5415_;
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
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5434_; 
lean_del_object(v___x_5370_);
lean_dec(v_fst_5367_);
lean_del_object(v___x_5363_);
lean_dec(v_fst_5360_);
lean_del_object(v___x_5356_);
lean_dec(v_fst_5353_);
lean_del_object(v___x_5349_);
lean_dec(v_fst_5346_);
lean_del_object(v___x_5342_);
lean_del_object(v___x_5338_);
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_del_object(v___x_5318_);
v_a_5427_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5429_ = v___x_5372_;
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5372_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5432_; 
if (v_isShared_5430_ == 0)
{
v___x_5432_ = v___x_5429_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_a_5427_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
}
}
}
else
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
lean_del_object(v___x_5363_);
lean_dec(v_fst_5360_);
lean_del_object(v___x_5356_);
lean_dec(v_fst_5353_);
lean_del_object(v___x_5349_);
lean_dec(v_fst_5346_);
lean_del_object(v___x_5342_);
lean_del_object(v___x_5338_);
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec(v_all_5322_);
lean_del_object(v___x_5318_);
v_a_5436_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5438_ = v___x_5365_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5365_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
}
else
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_del_object(v___x_5356_);
lean_dec(v_fst_5353_);
lean_del_object(v___x_5349_);
lean_dec(v_fst_5346_);
lean_del_object(v___x_5342_);
lean_del_object(v___x_5338_);
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec(v_all_5322_);
lean_dec_ref(v_value_5321_);
lean_del_object(v___x_5318_);
v_a_5445_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5358_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5358_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5445_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
lean_del_object(v___x_5349_);
lean_dec(v_fst_5346_);
lean_del_object(v___x_5342_);
lean_del_object(v___x_5338_);
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec_ref(v_type_5325_);
lean_dec(v_all_5322_);
lean_dec_ref(v_value_5321_);
lean_del_object(v___x_5318_);
v_a_5454_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5351_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5351_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_del_object(v___x_5342_);
lean_del_object(v___x_5338_);
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec_ref(v_type_5325_);
lean_dec(v_levelParams_5324_);
lean_dec(v_all_5322_);
lean_dec_ref(v_value_5321_);
lean_del_object(v___x_5318_);
v_a_5463_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5344_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5344_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5333_);
lean_del_object(v___x_5329_);
lean_dec_ref(v_type_5325_);
lean_dec(v_levelParams_5324_);
lean_dec(v_name_5323_);
lean_dec(v_all_5322_);
lean_dec_ref(v_value_5321_);
lean_del_object(v___x_5318_);
return v___x_5335_;
}
}
}
}
else
{
lean_dec_ref(v_type_5325_);
lean_dec(v_levelParams_5324_);
lean_dec(v_name_5323_);
lean_dec(v_all_5322_);
lean_dec_ref(v_value_5321_);
lean_del_object(v___x_5318_);
return v___x_5326_;
}
}
}
case 3:
{
lean_object* v_val_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5644_; 
v_val_5478_ = lean_ctor_get(v_val_5021_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v_val_5021_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5480_ = v_val_5021_;
v_isShared_5481_ = v_isSharedCheck_5644_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_val_5478_);
lean_dec(v_val_5021_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5644_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_toConstantVal_5482_; lean_object* v_value_5483_; uint8_t v_isUnsafe_5484_; lean_object* v_all_5485_; lean_object* v_name_5486_; lean_object* v_levelParams_5487_; lean_object* v_type_5488_; lean_object* v___x_5489_; 
v_toConstantVal_5482_ = lean_ctor_get(v_val_5478_, 0);
lean_inc_ref(v_toConstantVal_5482_);
v_value_5483_ = lean_ctor_get(v_val_5478_, 1);
lean_inc_ref(v_value_5483_);
v_isUnsafe_5484_ = lean_ctor_get_uint8(v_val_5478_, sizeof(void*)*3);
v_all_5485_ = lean_ctor_get(v_val_5478_, 2);
lean_inc(v_all_5485_);
lean_dec_ref(v_val_5478_);
v_name_5486_ = lean_ctor_get(v_toConstantVal_5482_, 0);
lean_inc(v_name_5486_);
v_levelParams_5487_ = lean_ctor_get(v_toConstantVal_5482_, 1);
lean_inc(v_levelParams_5487_);
v_type_5488_ = lean_ctor_get(v_toConstantVal_5482_, 2);
lean_inc_ref_n(v_type_5488_, 2);
lean_dec_ref(v_toConstantVal_5482_);
v___x_5489_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5488_, v_a_4910_, v___x_5038_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5643_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5643_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5492_ = v___x_5489_;
v_isShared_5493_ = v_isSharedCheck_5643_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5489_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5643_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v_snd_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5641_; 
v_snd_5494_ = lean_ctor_get(v_a_5490_, 1);
v_isSharedCheck_5641_ = !lean_is_exclusive(v_a_5490_);
if (v_isSharedCheck_5641_ == 0)
{
lean_object* v_unused_5642_; 
v_unused_5642_ = lean_ctor_get(v_a_5490_, 0);
lean_dec(v_unused_5642_);
v___x_5496_ = v_a_5490_;
v_isShared_5497_ = v_isSharedCheck_5641_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_snd_5494_);
lean_dec(v_a_5490_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5641_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5498_; 
lean_inc_ref(v_value_5483_);
v___x_5498_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5483_, v_a_4910_, v_snd_5494_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5640_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5501_ = v___x_5498_;
v_isShared_5502_ = v_isSharedCheck_5640_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5498_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5640_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v_snd_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5638_; 
v_snd_5503_ = lean_ctor_get(v_a_5499_, 1);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_a_5499_);
if (v_isSharedCheck_5638_ == 0)
{
lean_object* v_unused_5639_; 
v_unused_5639_ = lean_ctor_get(v_a_5499_, 0);
lean_dec(v_unused_5639_);
v___x_5505_ = v_a_5499_;
v_isShared_5506_ = v_isSharedCheck_5638_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_snd_5503_);
lean_dec(v_a_5499_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5638_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; 
v___x_5507_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5486_, v_a_4910_, v_snd_5503_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v_fst_5509_; lean_object* v_snd_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5629_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref_known(v___x_5507_, 1);
v_fst_5509_ = lean_ctor_get(v_a_5508_, 0);
v_snd_5510_ = lean_ctor_get(v_a_5508_, 1);
v_isSharedCheck_5629_ = !lean_is_exclusive(v_a_5508_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5512_ = v_a_5508_;
v_isShared_5513_ = v_isSharedCheck_5629_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_snd_5510_);
lean_inc(v_fst_5509_);
lean_dec(v_a_5508_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5629_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5514_; 
v___x_5514_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5487_, v_a_4910_, v_snd_5510_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v_fst_5516_; lean_object* v_snd_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5620_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref_known(v___x_5514_, 1);
v_fst_5516_ = lean_ctor_get(v_a_5515_, 0);
v_snd_5517_ = lean_ctor_get(v_a_5515_, 1);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_a_5515_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5519_ = v_a_5515_;
v_isShared_5520_ = v_isSharedCheck_5620_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_snd_5517_);
lean_inc(v_fst_5516_);
lean_dec(v_a_5515_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5620_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; 
v___x_5521_ = l_LeanExport_dumpExpr(v_type_5488_, v_a_4910_, v_snd_5517_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; lean_object* v_fst_5523_; lean_object* v_snd_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5611_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5521_, 1);
v_fst_5523_ = lean_ctor_get(v_a_5522_, 0);
v_snd_5524_ = lean_ctor_get(v_a_5522_, 1);
v_isSharedCheck_5611_ = !lean_is_exclusive(v_a_5522_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5526_ = v_a_5522_;
v_isShared_5527_ = v_isSharedCheck_5611_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_snd_5524_);
lean_inc(v_fst_5523_);
lean_dec(v_a_5522_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5611_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5528_; 
v___x_5528_ = l_LeanExport_dumpExpr(v_value_5483_, v_a_4910_, v_snd_5524_);
if (lean_obj_tag(v___x_5528_) == 0)
{
lean_object* v_a_5529_; lean_object* v_fst_5530_; lean_object* v_snd_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5602_; 
v_a_5529_ = lean_ctor_get(v___x_5528_, 0);
lean_inc(v_a_5529_);
lean_dec_ref_known(v___x_5528_, 1);
v_fst_5530_ = lean_ctor_get(v_a_5529_, 0);
v_snd_5531_ = lean_ctor_get(v_a_5529_, 1);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_a_5529_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5533_ = v_a_5529_;
v_isShared_5534_ = v_isSharedCheck_5602_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_snd_5531_);
lean_inc(v_fst_5530_);
lean_dec(v_a_5529_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5602_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5535_; 
v___x_5535_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5485_, v_a_4910_, v_snd_5531_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v_fst_5537_; lean_object* v_snd_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5593_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
lean_dec_ref_known(v___x_5535_, 1);
v_fst_5537_ = lean_ctor_get(v_a_5536_, 0);
v_snd_5538_ = lean_ctor_get(v_a_5536_, 1);
v_isSharedCheck_5593_ = !lean_is_exclusive(v_a_5536_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5540_ = v_a_5536_;
v_isShared_5541_ = v_isSharedCheck_5593_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_snd_5538_);
lean_inc(v_fst_5537_);
lean_dec(v_a_5536_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5593_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5542_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5544_ = l_Lean_JsonNumber_fromNat(v_fst_5509_);
if (v_isShared_5502_ == 0)
{
lean_ctor_set_tag(v___x_5501_, 2);
lean_ctor_set(v___x_5501_, 0, v___x_5544_);
v___x_5546_ = v___x_5501_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5544_);
v___x_5546_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5548_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5546_);
lean_ctor_set(v___x_5540_, 0, v___x_5543_);
v___x_5548_ = v___x_5540_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v_fst_5516_);
lean_ctor_set(v___x_5533_, 0, v___x_5549_);
v___x_5551_ = v___x_5533_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5549_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_fst_5516_);
v___x_5551_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5555_; 
v___x_5552_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5553_ = l_Lean_JsonNumber_fromNat(v_fst_5523_);
if (v_isShared_5493_ == 0)
{
lean_ctor_set_tag(v___x_5492_, 2);
lean_ctor_set(v___x_5492_, 0, v___x_5553_);
v___x_5555_ = v___x_5492_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5557_; 
if (v_isShared_5527_ == 0)
{
lean_ctor_set(v___x_5526_, 1, v___x_5555_);
lean_ctor_set(v___x_5526_, 0, v___x_5552_);
v___x_5557_ = v___x_5526_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5561_; 
v___x_5558_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5559_ = l_Lean_JsonNumber_fromNat(v_fst_5530_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set_tag(v___x_5480_, 2);
lean_ctor_set(v___x_5480_, 0, v___x_5559_);
v___x_5561_ = v___x_5480_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5559_);
v___x_5561_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 1, v___x_5561_);
lean_ctor_set(v___x_5519_, 0, v___x_5558_);
v___x_5563_ = v___x_5519_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5564_; lean_object* v___x_5566_; 
v___x_5564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v_fst_5537_);
lean_ctor_set(v___x_5512_, 0, v___x_5564_);
v___x_5566_ = v___x_5512_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_fst_5537_);
v___x_5566_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_5568_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5568_, 0, v_isUnsafe_5484_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 1, v___x_5568_);
lean_ctor_set(v___x_5505_, 0, v___x_5567_);
v___x_5570_ = v___x_5505_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5567_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5580_; 
v___x_5571_ = lean_box(0);
v___x_5572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5570_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___x_5573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5566_);
lean_ctor_set(v___x_5573_, 1, v___x_5572_);
v___x_5574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5574_, 0, v___x_5563_);
lean_ctor_set(v___x_5574_, 1, v___x_5573_);
v___x_5575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5557_);
lean_ctor_set(v___x_5575_, 1, v___x_5574_);
v___x_5576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5551_);
lean_ctor_set(v___x_5576_, 1, v___x_5575_);
v___x_5577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5548_);
lean_ctor_set(v___x_5577_, 1, v___x_5576_);
v___x_5578_ = l_Lean_Json_mkObj(v___x_5577_);
lean_dec_ref_known(v___x_5577_, 2);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5578_);
lean_ctor_set(v___x_5496_, 0, v___x_5542_);
v___x_5580_ = v___x_5496_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5542_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5581_, 0, v___x_5580_);
lean_ctor_set(v___x_5581_, 1, v___x_5571_);
v___x_5582_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5581_, v_snd_5538_);
lean_dec_ref_known(v___x_5581_, 2);
return v___x_5582_;
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
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5601_; 
lean_del_object(v___x_5533_);
lean_dec(v_fst_5530_);
lean_del_object(v___x_5526_);
lean_dec(v_fst_5523_);
lean_del_object(v___x_5519_);
lean_dec(v_fst_5516_);
lean_del_object(v___x_5512_);
lean_dec(v_fst_5509_);
lean_del_object(v___x_5505_);
lean_del_object(v___x_5501_);
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_del_object(v___x_5480_);
v_a_5594_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5535_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5535_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5594_);
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
lean_object* v_a_5603_; lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5610_; 
lean_del_object(v___x_5526_);
lean_dec(v_fst_5523_);
lean_del_object(v___x_5519_);
lean_dec(v_fst_5516_);
lean_del_object(v___x_5512_);
lean_dec(v_fst_5509_);
lean_del_object(v___x_5505_);
lean_del_object(v___x_5501_);
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_dec(v_all_5485_);
lean_del_object(v___x_5480_);
v_a_5603_ = lean_ctor_get(v___x_5528_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5605_ = v___x_5528_;
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
else
{
lean_inc(v_a_5603_);
lean_dec(v___x_5528_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5608_; 
if (v_isShared_5606_ == 0)
{
v___x_5608_ = v___x_5605_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
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
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_del_object(v___x_5519_);
lean_dec(v_fst_5516_);
lean_del_object(v___x_5512_);
lean_dec(v_fst_5509_);
lean_del_object(v___x_5505_);
lean_del_object(v___x_5501_);
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_dec(v_all_5485_);
lean_dec_ref(v_value_5483_);
lean_del_object(v___x_5480_);
v_a_5612_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5521_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5521_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_del_object(v___x_5512_);
lean_dec(v_fst_5509_);
lean_del_object(v___x_5505_);
lean_del_object(v___x_5501_);
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_dec_ref(v_type_5488_);
lean_dec(v_all_5485_);
lean_dec_ref(v_value_5483_);
lean_del_object(v___x_5480_);
v_a_5621_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5514_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5514_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
else
{
lean_object* v_a_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5637_; 
lean_del_object(v___x_5505_);
lean_del_object(v___x_5501_);
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_dec_ref(v_type_5488_);
lean_dec(v_levelParams_5487_);
lean_dec(v_all_5485_);
lean_dec_ref(v_value_5483_);
lean_del_object(v___x_5480_);
v_a_5630_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5637_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5632_ = v___x_5507_;
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_a_5630_);
lean_dec(v___x_5507_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5635_; 
if (v_isShared_5633_ == 0)
{
v___x_5635_ = v___x_5632_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_a_5630_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5496_);
lean_del_object(v___x_5492_);
lean_dec_ref(v_type_5488_);
lean_dec(v_levelParams_5487_);
lean_dec(v_name_5486_);
lean_dec(v_all_5485_);
lean_dec_ref(v_value_5483_);
lean_del_object(v___x_5480_);
return v___x_5498_;
}
}
}
}
else
{
lean_dec_ref(v_type_5488_);
lean_dec(v_levelParams_5487_);
lean_dec(v_name_5486_);
lean_dec(v_all_5485_);
lean_dec_ref(v_value_5483_);
lean_del_object(v___x_5480_);
return v___x_5489_;
}
}
}
case 4:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; 
lean_dec_ref_known(v_val_5021_, 1);
v___x_5645_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5646_ = l_LeanExport_dumpConstant(v___x_5645_, v_a_4910_, v___x_5038_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v_snd_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc(v_a_5647_);
lean_dec_ref_known(v___x_5646_, 1);
v_snd_5648_ = lean_ctor_get(v_a_5647_, 1);
lean_inc(v_snd_5648_);
lean_dec(v_a_5647_);
v___x_5649_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5650_ = lean_box(0);
v___x_5651_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5652_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5032_, v___x_5649_, v___x_5651_, v_a_4910_, v_snd_5648_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5679_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5655_ = v___x_5652_;
v_isShared_5656_ = v_isSharedCheck_5679_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5652_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5679_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v_fst_5657_; lean_object* v_fst_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5677_; 
v_fst_5657_ = lean_ctor_get(v_a_5653_, 0);
lean_inc(v_fst_5657_);
v_fst_5658_ = lean_ctor_get(v_fst_5657_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_fst_5657_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; 
v_unused_5678_ = lean_ctor_get(v_fst_5657_, 1);
lean_dec(v_unused_5678_);
v___x_5660_ = v_fst_5657_;
v_isShared_5661_ = v_isSharedCheck_5677_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_fst_5658_);
lean_dec(v_fst_5657_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5677_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
if (lean_obj_tag(v_fst_5658_) == 0)
{
lean_object* v_snd_5662_; lean_object* v___x_5664_; 
v_snd_5662_ = lean_ctor_get(v_a_5653_, 1);
lean_inc(v_snd_5662_);
lean_dec(v_a_5653_);
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 1, v_snd_5662_);
lean_ctor_set(v___x_5660_, 0, v___x_5650_);
v___x_5664_ = v___x_5660_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_snd_5662_);
v___x_5664_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5666_; 
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 0, v___x_5664_);
v___x_5666_ = v___x_5655_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5664_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
else
{
lean_object* v_snd_5669_; lean_object* v_val_5670_; lean_object* v___x_5672_; 
v_snd_5669_ = lean_ctor_get(v_a_5653_, 1);
lean_inc(v_snd_5669_);
lean_dec(v_a_5653_);
v_val_5670_ = lean_ctor_get(v_fst_5658_, 0);
lean_inc(v_val_5670_);
lean_dec_ref_known(v_fst_5658_, 1);
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 1, v_snd_5669_);
lean_ctor_set(v___x_5660_, 0, v_val_5670_);
v___x_5672_ = v___x_5660_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_val_5670_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v_snd_5669_);
v___x_5672_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 0, v___x_5672_);
v___x_5674_ = v___x_5655_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5672_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
v_a_5680_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5652_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5652_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
else
{
return v___x_5646_;
}
}
case 5:
{
lean_object* v_val_5688_; lean_object* v_all_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v_val_5688_ = lean_ctor_get(v_val_5021_, 0);
lean_inc_ref(v_val_5688_);
lean_dec_ref_known(v_val_5021_, 1);
v_all_5689_ = lean_ctor_get(v_val_5688_, 3);
lean_inc(v_all_5689_);
v___x_5690_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5691_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5692_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5032_, v_val_5688_, v_all_5689_, v___x_5691_, v_a_4910_, v___x_5038_);
lean_dec(v_all_5689_);
lean_dec_ref(v_val_5688_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_object* v_a_5693_; lean_object* v_fst_5694_; lean_object* v_snd_5695_; lean_object* v_snd_5696_; lean_object* v_fst_5697_; lean_object* v_fst_5698_; lean_object* v_snd_5699_; lean_object* v___x_5700_; size_t v_sz_5701_; size_t v___x_5702_; lean_object* v___x_5703_; 
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_a_5693_);
lean_dec_ref_known(v___x_5692_, 1);
v_fst_5694_ = lean_ctor_get(v_a_5693_, 0);
lean_inc(v_fst_5694_);
v_snd_5695_ = lean_ctor_get(v_fst_5694_, 1);
lean_inc(v_snd_5695_);
v_snd_5696_ = lean_ctor_get(v_a_5693_, 1);
lean_inc(v_snd_5696_);
lean_dec(v_a_5693_);
v_fst_5697_ = lean_ctor_get(v_fst_5694_, 0);
lean_inc(v_fst_5697_);
lean_dec(v_fst_5694_);
v_fst_5698_ = lean_ctor_get(v_snd_5695_, 0);
lean_inc(v_fst_5698_);
v_snd_5699_ = lean_ctor_get(v_snd_5695_, 1);
lean_inc(v_snd_5699_);
lean_dec(v_snd_5695_);
v___x_5700_ = lean_box(0);
v_sz_5701_ = lean_array_size(v_fst_5698_);
v___x_5702_ = ((size_t)0ULL);
v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_fst_5698_, v_sz_5701_, v___x_5702_, v___x_5700_, v_a_4910_, v_snd_5696_);
if (lean_obj_tag(v___x_5703_) == 0)
{
lean_object* v_a_5704_; lean_object* v_snd_5705_; lean_object* v___x_5706_; 
v_a_5704_ = lean_ctor_get(v___x_5703_, 0);
lean_inc(v_a_5704_);
lean_dec_ref_known(v___x_5703_, 1);
v_snd_5705_ = lean_ctor_get(v_a_5704_, 1);
lean_inc(v_snd_5705_);
lean_dec(v_a_5704_);
v___x_5706_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_5032_, v___x_5690_, v_snd_5699_, v_a_4910_, v_snd_5705_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v_a_5707_; lean_object* v_fst_5708_; lean_object* v_snd_5709_; lean_object* v_a_5710_; 
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
lean_inc(v_a_5707_);
lean_dec_ref_known(v___x_5706_, 1);
v_fst_5708_ = lean_ctor_get(v_a_5707_, 0);
lean_inc(v_fst_5708_);
v_snd_5709_ = lean_ctor_get(v_a_5707_, 1);
lean_inc(v_snd_5709_);
lean_dec(v_a_5707_);
v_a_5710_ = lean_ctor_get(v_fst_5708_, 0);
lean_inc(v_a_5710_);
lean_dec(v_fst_5708_);
v___y_4918_ = v___x_5700_;
v___y_4919_ = v_fst_5697_;
v___y_4920_ = v_fst_5698_;
v_fst_4921_ = v_a_5710_;
v_snd_4922_ = v_snd_5709_;
goto v___jp_4917_;
}
else
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5718_; 
lean_dec(v_fst_5698_);
lean_dec(v_fst_5697_);
v_a_5711_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5718_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5718_ == 0)
{
v___x_5713_ = v___x_5706_;
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v___x_5706_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5716_; 
if (v_isShared_5714_ == 0)
{
v___x_5716_ = v___x_5713_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5711_);
v___x_5716_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
return v___x_5716_;
}
}
}
}
else
{
lean_dec(v_snd_5699_);
lean_dec(v_fst_5698_);
lean_dec(v_fst_5697_);
return v___x_5703_;
}
}
else
{
lean_object* v_a_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5726_; 
v_a_5719_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5726_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5726_ == 0)
{
v___x_5721_ = v___x_5692_;
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_a_5719_);
lean_dec(v___x_5692_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5724_; 
if (v_isShared_5722_ == 0)
{
v___x_5724_ = v___x_5721_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_a_5719_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
case 6:
{
lean_object* v_val_5727_; lean_object* v_induct_5728_; 
v_val_5727_ = lean_ctor_get(v_val_5021_, 0);
lean_inc_ref(v_val_5727_);
lean_dec_ref_known(v_val_5021_, 1);
v_induct_5728_ = lean_ctor_get(v_val_5727_, 1);
lean_inc(v_induct_5728_);
lean_dec_ref(v_val_5727_);
v_c_4909_ = v_induct_5728_;
v_a_4911_ = v___x_5038_;
goto _start;
}
default: 
{
lean_object* v_val_5730_; lean_object* v_all_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
v_val_5730_ = lean_ctor_get(v_val_5021_, 0);
lean_inc_ref(v_val_5730_);
lean_dec_ref_known(v_val_5021_, 1);
v_all_5731_ = lean_ctor_get(v_val_5730_, 1);
lean_inc(v_all_5731_);
lean_dec_ref(v_val_5730_);
v___x_5732_ = lean_box(0);
v___x_5733_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5731_, v___x_5732_, v_a_4910_, v___x_5038_);
lean_dec(v_all_5731_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5750_; 
v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5736_ = v___x_5733_;
v_isShared_5737_ = v_isSharedCheck_5750_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5733_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5750_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_snd_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5748_; 
v_snd_5738_ = lean_ctor_get(v_a_5734_, 1);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_a_5734_);
if (v_isSharedCheck_5748_ == 0)
{
lean_object* v_unused_5749_; 
v_unused_5749_ = lean_ctor_get(v_a_5734_, 0);
lean_dec(v_unused_5749_);
v___x_5740_ = v_a_5734_;
v_isShared_5741_ = v_isSharedCheck_5748_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_snd_5738_);
lean_dec(v_a_5734_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5748_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 0, v___x_5732_);
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5732_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v_snd_5738_);
v___x_5743_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5745_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 0, v___x_5743_);
v___x_5745_ = v___x_5736_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
}
}
else
{
return v___x_5733_;
}
}
}
}
}
}
else
{
lean_dec(v_val_5021_);
lean_dec(v_c_4909_);
goto v___jp_4913_;
}
}
}
else
{
uint8_t v_ignoreMissing_5761_; 
lean_dec(v___x_5020_);
v_ignoreMissing_5761_ = lean_ctor_get_uint8(v_a_4911_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5761_ == 0)
{
lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; uint8_t v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v___x_5762_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5763_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_5764_ = lean_unsigned_to_nat(254u);
v___x_5765_ = lean_unsigned_to_nat(48u);
v___x_5766_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5767_ = 1;
v___x_5768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4909_, v___x_5767_);
v___x_5769_ = lean_string_append(v___x_5766_, v___x_5768_);
lean_dec_ref(v___x_5768_);
v___x_5770_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5771_ = lean_string_append(v___x_5769_, v___x_5770_);
v___x_5772_ = l_mkPanicMessageWithDecl(v___x_5762_, v___x_5763_, v___x_5764_, v___x_5765_, v___x_5771_);
lean_dec_ref(v___x_5771_);
v___x_5773_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5772_, v_a_4910_, v_a_4911_);
return v___x_5773_;
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; 
lean_dec(v_c_4909_);
v___x_5774_ = lean_box(0);
v___x_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5774_);
lean_ctor_set(v___x_5775_, 1, v_a_4911_);
v___x_5776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5776_, 0, v___x_5775_);
return v___x_5776_;
}
}
v___jp_4913_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4914_ = lean_box(0);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
lean_ctor_set(v___x_4915_, 1, v_a_4911_);
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
return v___x_4916_;
}
v___jp_4917_:
{
size_t v_sz_4923_; size_t v___x_4924_; lean_object* v___x_4925_; 
v_sz_4923_ = lean_array_size(v_fst_4921_);
v___x_4924_ = ((size_t)0ULL);
v___x_4925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_4921_, v_sz_4923_, v___x_4924_, v___y_4918_, v_a_4910_, v_snd_4922_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v_snd_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_5017_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4926_);
lean_dec_ref_known(v___x_4925_, 1);
v_snd_4927_ = lean_ctor_get(v_a_4926_, 1);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_a_4926_);
if (v_isSharedCheck_5017_ == 0)
{
lean_object* v_unused_5018_; 
v_unused_5018_ = lean_ctor_get(v_a_4926_, 0);
lean_dec(v_unused_5018_);
v___x_4929_ = v_a_4926_;
v_isShared_4930_ = v_isSharedCheck_5017_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_snd_4927_);
lean_dec(v_a_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_5017_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; 
v___x_4931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_fst_4921_, v_sz_4923_, v___x_4924_, v___y_4918_, v_a_4910_, v_snd_4927_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v_snd_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_5015_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
v_snd_4933_ = lean_ctor_get(v_a_4932_, 1);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_a_4932_);
if (v_isSharedCheck_5015_ == 0)
{
lean_object* v_unused_5016_; 
v_unused_5016_ = lean_ctor_get(v_a_4932_, 0);
lean_dec(v_unused_5016_);
v___x_4935_ = v_a_4932_;
v_isShared_4936_ = v_isSharedCheck_5015_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_snd_4933_);
lean_dec(v_a_4932_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_5015_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
size_t v_sz_4937_; lean_object* v___x_4938_; 
v_sz_4937_ = lean_array_size(v___y_4919_);
v___x_4938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_4937_, v___x_4924_, v___y_4919_, v_a_4910_, v_snd_4933_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v_fst_4940_; lean_object* v_snd_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_5006_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v_fst_4940_ = lean_ctor_get(v_a_4939_, 0);
v_snd_4941_ = lean_ctor_get(v_a_4939_, 1);
v_isSharedCheck_5006_ = !lean_is_exclusive(v_a_4939_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4943_ = v_a_4939_;
v_isShared_4944_ = v_isSharedCheck_5006_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_snd_4941_);
lean_inc(v_fst_4940_);
lean_dec(v_a_4939_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_5006_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
size_t v_sz_4945_; lean_object* v___x_4946_; 
v_sz_4945_ = lean_array_size(v___y_4920_);
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_4945_, v___x_4924_, v___y_4920_, v_a_4910_, v_snd_4941_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v_fst_4948_; lean_object* v_snd_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4997_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v_fst_4948_ = lean_ctor_get(v_a_4947_, 0);
v_snd_4949_ = lean_ctor_get(v_a_4947_, 1);
v_isSharedCheck_4997_ = !lean_is_exclusive(v_a_4947_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4951_ = v_a_4947_;
v_isShared_4952_ = v_isSharedCheck_4997_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_snd_4949_);
lean_inc(v_fst_4948_);
lean_dec(v_a_4947_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4997_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4953_; 
v___x_4953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4923_, v___x_4924_, v_fst_4921_, v_a_4910_, v_snd_4949_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v_a_4954_; lean_object* v_fst_4955_; lean_object* v_snd_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4988_; 
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
lean_inc(v_a_4954_);
lean_dec_ref_known(v___x_4953_, 1);
v_fst_4955_ = lean_ctor_get(v_a_4954_, 0);
v_snd_4956_ = lean_ctor_get(v_a_4954_, 1);
v_isSharedCheck_4988_ = !lean_is_exclusive(v_a_4954_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4958_ = v_a_4954_;
v_isShared_4959_ = v_isSharedCheck_4988_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_snd_4956_);
lean_inc(v_fst_4955_);
lean_dec(v_a_4954_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4988_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4964_; 
v___x_4960_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4961_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4962_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4940_);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 1, v___x_4962_);
lean_ctor_set(v___x_4958_, 0, v___x_4961_);
v___x_4964_ = v___x_4958_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4961_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v___x_4962_);
v___x_4964_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_4966_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4948_);
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_4966_);
lean_ctor_set(v___x_4951_, 0, v___x_4965_);
v___x_4968_ = v___x_4951_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4965_);
lean_ctor_set(v_reuseFailAlloc_4986_, 1, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4972_; 
v___x_4969_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4970_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4955_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_4970_);
lean_ctor_set(v___x_4943_, 0, v___x_4969_);
v___x_4972_ = v___x_4943_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4969_);
lean_ctor_set(v_reuseFailAlloc_4985_, 1, v___x_4970_);
v___x_4972_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
lean_object* v___x_4973_; lean_object* v___x_4975_; 
v___x_4973_ = lean_box(0);
if (v_isShared_4930_ == 0)
{
lean_ctor_set_tag(v___x_4929_, 1);
lean_ctor_set(v___x_4929_, 1, v___x_4973_);
lean_ctor_set(v___x_4929_, 0, v___x_4972_);
v___x_4975_ = v___x_4929_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4972_);
lean_ctor_set(v_reuseFailAlloc_4984_, 1, v___x_4973_);
v___x_4975_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4980_; 
v___x_4976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4968_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4964_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
v___x_4978_ = l_Lean_Json_mkObj(v___x_4977_);
lean_dec_ref_known(v___x_4977_, 2);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 1, v___x_4978_);
lean_ctor_set(v___x_4935_, 0, v___x_4960_);
v___x_4980_ = v___x_4935_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v___x_4960_);
lean_ctor_set(v_reuseFailAlloc_4983_, 1, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
lean_ctor_set(v___x_4981_, 1, v___x_4973_);
v___x_4982_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4981_, v_snd_4956_);
lean_dec_ref_known(v___x_4981_, 2);
return v___x_4982_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_del_object(v___x_4951_);
lean_dec(v_fst_4948_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4940_);
lean_del_object(v___x_4935_);
lean_del_object(v___x_4929_);
v_a_4989_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4953_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4953_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_del_object(v___x_4943_);
lean_dec(v_fst_4940_);
lean_del_object(v___x_4935_);
lean_del_object(v___x_4929_);
lean_dec_ref(v_fst_4921_);
v_a_4998_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4946_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4946_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_del_object(v___x_4935_);
lean_del_object(v___x_4929_);
lean_dec_ref(v_fst_4921_);
lean_dec(v___y_4920_);
v_a_5007_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4938_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4938_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
}
else
{
lean_del_object(v___x_4929_);
lean_dec_ref(v_fst_4921_);
lean_dec(v___y_4920_);
lean_dec(v___y_4919_);
return v___x_4931_;
}
}
}
else
{
lean_dec_ref(v_fst_4921_);
lean_dec(v___y_4920_);
lean_dec(v___y_4919_);
return v___x_4925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5777_, size_t v_sz_5778_, size_t v_i_5779_, lean_object* v_b_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
uint8_t v___x_5784_; 
v___x_5784_ = lean_usize_dec_lt(v_i_5779_, v_sz_5778_);
if (v___x_5784_ == 0)
{
lean_object* v___x_5785_; lean_object* v___x_5786_; 
v___x_5785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5785_, 0, v_b_5780_);
lean_ctor_set(v___x_5785_, 1, v___y_5782_);
v___x_5786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5785_);
return v___x_5786_;
}
else
{
lean_object* v___x_5787_; lean_object* v_a_5788_; lean_object* v___x_5789_; 
v___x_5787_ = lean_box(0);
v_a_5788_ = lean_array_uget_borrowed(v_as_5777_, v_i_5779_);
lean_inc(v_a_5788_);
v___x_5789_ = l_LeanExport_dumpConstant(v_a_5788_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v_snd_5791_; size_t v___x_5792_; size_t v___x_5793_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
lean_inc(v_a_5790_);
lean_dec_ref_known(v___x_5789_, 1);
v_snd_5791_ = lean_ctor_get(v_a_5790_, 1);
lean_inc(v_snd_5791_);
lean_dec(v_a_5790_);
v___x_5792_ = ((size_t)1ULL);
v___x_5793_ = lean_usize_add(v_i_5779_, v___x_5792_);
v_i_5779_ = v___x_5793_;
v_b_5780_ = v___x_5787_;
v___y_5782_ = v_snd_5791_;
goto _start;
}
else
{
return v___x_5789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; size_t v_sz_5801_; size_t v___x_5802_; lean_object* v___x_5803_; 
v___x_5799_ = l_Lean_Expr_getUsedConstants(v_e_5795_);
v___x_5800_ = lean_box(0);
v_sz_5801_ = lean_array_size(v___x_5799_);
v___x_5802_ = ((size_t)0ULL);
v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5799_, v_sz_5801_, v___x_5802_, v___x_5800_, v_a_5796_, v_a_5797_);
lean_dec_ref(v___x_5799_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5820_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5820_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5806_ = v___x_5803_;
v_isShared_5807_ = v_isSharedCheck_5820_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_a_5804_);
lean_dec(v___x_5803_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5820_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v_snd_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5818_; 
v_snd_5808_ = lean_ctor_get(v_a_5804_, 1);
v_isSharedCheck_5818_ = !lean_is_exclusive(v_a_5804_);
if (v_isSharedCheck_5818_ == 0)
{
lean_object* v_unused_5819_; 
v_unused_5819_ = lean_ctor_get(v_a_5804_, 0);
lean_dec(v_unused_5819_);
v___x_5810_ = v_a_5804_;
v_isShared_5811_ = v_isSharedCheck_5818_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_snd_5808_);
lean_dec(v_a_5804_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5818_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v___x_5813_; 
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 0, v___x_5800_);
v___x_5813_ = v___x_5810_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5800_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v_snd_5808_);
v___x_5813_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
lean_object* v___x_5815_; 
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 0, v___x_5813_);
v___x_5815_ = v___x_5806_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
}
else
{
return v___x_5803_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5821_, v_a_5822_, v_a_5823_);
lean_dec_ref(v_a_5822_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5826_, lean_object* v_b_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_){
_start:
{
lean_object* v_res_5831_; 
v_res_5831_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5826_, v_b_5827_, v___y_5828_, v___y_5829_);
lean_dec_ref(v___y_5828_);
lean_dec(v_as_x27_5826_);
return v_res_5831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5832_, lean_object* v_b_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5832_, v_b_5833_, v___y_5834_, v___y_5835_);
lean_dec_ref(v___y_5834_);
lean_dec(v_as_x27_5832_);
return v_res_5837_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5838_, lean_object* v_x_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_){
_start:
{
lean_object* v_res_5843_; 
v_res_5843_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5838_, v_x_5839_, v___y_5840_, v___y_5841_);
lean_dec_ref(v___y_5840_);
return v_res_5843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5844_, lean_object* v_sz_5845_, lean_object* v_i_5846_, lean_object* v_b_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_){
_start:
{
size_t v_sz_boxed_5851_; size_t v_i_boxed_5852_; lean_object* v_res_5853_; 
v_sz_boxed_5851_ = lean_unbox_usize(v_sz_5845_);
lean_dec(v_sz_5845_);
v_i_boxed_5852_ = lean_unbox_usize(v_i_5846_);
lean_dec(v_i_5846_);
v_res_5853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5844_, v_sz_boxed_5851_, v_i_boxed_5852_, v_b_5847_, v___y_5848_, v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec_ref(v_as_5844_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5854_, v_a_5855_);
lean_dec_ref(v_a_5854_);
return v_res_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v_as_5858_, lean_object* v_sz_5859_, lean_object* v_i_5860_, lean_object* v_b_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_){
_start:
{
size_t v_sz_boxed_5865_; size_t v_i_boxed_5866_; lean_object* v_res_5867_; 
v_sz_boxed_5865_ = lean_unbox_usize(v_sz_5859_);
lean_dec(v_sz_5859_);
v_i_boxed_5866_ = lean_unbox_usize(v_i_5860_);
lean_dec(v_i_5860_);
v_res_5867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_as_5858_, v_sz_boxed_5865_, v_i_boxed_5866_, v_b_5861_, v___y_5862_, v___y_5863_);
lean_dec_ref(v___y_5862_);
lean_dec_ref(v_as_5858_);
return v_res_5867_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_){
_start:
{
lean_object* v_res_5872_; 
v_res_5872_ = l_LeanExport_dumpExpr(v_e_5868_, v_a_5869_, v_a_5870_);
lean_dec_ref(v_a_5869_);
return v_res_5872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5873_, lean_object* v_sz_5874_, lean_object* v_i_5875_, lean_object* v_b_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
size_t v_sz_boxed_5880_; size_t v_i_boxed_5881_; lean_object* v_res_5882_; 
v_sz_boxed_5880_ = lean_unbox_usize(v_sz_5874_);
lean_dec(v_sz_5874_);
v_i_boxed_5881_ = lean_unbox_usize(v_i_5875_);
lean_dec(v_i_5875_);
v_res_5882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5873_, v_sz_boxed_5880_, v_i_boxed_5881_, v_b_5876_, v___y_5877_, v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec_ref(v_as_5873_);
return v_res_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_as_5883_, lean_object* v_sz_5884_, lean_object* v_i_5885_, lean_object* v_b_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_){
_start:
{
size_t v_sz_boxed_5890_; size_t v_i_boxed_5891_; lean_object* v_res_5892_; 
v_sz_boxed_5890_ = lean_unbox_usize(v_sz_5884_);
lean_dec(v_sz_5884_);
v_i_boxed_5891_ = lean_unbox_usize(v_i_5885_);
lean_dec(v_i_5885_);
v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_as_5883_, v_sz_boxed_5890_, v_i_boxed_5891_, v_b_5886_, v___y_5887_, v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec_ref(v_as_5883_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_, lean_object* v_a_5896_){
_start:
{
lean_object* v_res_5897_; 
v_res_5897_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5893_, v_a_5894_, v_a_5895_);
lean_dec_ref(v_a_5894_);
return v_res_5897_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_){
_start:
{
lean_object* v_res_5901_; 
v_res_5901_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5898_, v_a_5899_);
lean_dec_ref(v_a_5898_);
return v_res_5901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_sz_5902_, lean_object* v_i_5903_, lean_object* v_bs_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
size_t v_sz_boxed_5908_; size_t v_i_boxed_5909_; lean_object* v_res_5910_; 
v_sz_boxed_5908_ = lean_unbox_usize(v_sz_5902_);
lean_dec(v_sz_5902_);
v_i_boxed_5909_ = lean_unbox_usize(v_i_5903_);
lean_dec(v_i_5903_);
v_res_5910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_boxed_5908_, v_i_boxed_5909_, v_bs_5904_, v___y_5905_, v___y_5906_);
lean_dec_ref(v___y_5905_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_sz_5911_, lean_object* v_i_5912_, lean_object* v_bs_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_){
_start:
{
size_t v_sz_boxed_5917_; size_t v_i_boxed_5918_; lean_object* v_res_5919_; 
v_sz_boxed_5917_ = lean_unbox_usize(v_sz_5911_);
lean_dec(v_sz_5911_);
v_i_boxed_5918_ = lean_unbox_usize(v_i_5912_);
lean_dec(v_i_5912_);
v_res_5919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_boxed_5917_, v_i_boxed_5918_, v_bs_5913_, v___y_5914_, v___y_5915_);
lean_dec_ref(v___y_5914_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object* v_sz_5920_, lean_object* v_i_5921_, lean_object* v_bs_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
size_t v_sz_boxed_5926_; size_t v_i_boxed_5927_; lean_object* v_res_5928_; 
v_sz_boxed_5926_ = lean_unbox_usize(v_sz_5920_);
lean_dec(v_sz_5920_);
v_i_boxed_5927_ = lean_unbox_usize(v_i_5921_);
lean_dec(v_i_5921_);
v_res_5928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_boxed_5926_, v_i_boxed_5927_, v_bs_5922_, v___y_5923_, v___y_5924_);
lean_dec_ref(v___y_5923_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5929_, lean_object* v_as_x27_5930_, lean_object* v_b_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_){
_start:
{
uint8_t v___x_173317__boxed_5935_; lean_object* v_res_5936_; 
v___x_173317__boxed_5935_ = lean_unbox(v___x_5929_);
v_res_5936_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173317__boxed_5935_, v_as_x27_5930_, v_b_5931_, v___y_5932_, v___y_5933_);
lean_dec_ref(v___y_5932_);
lean_dec(v_as_x27_5930_);
return v_res_5936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5937_, lean_object* v_val_5938_, lean_object* v_as_x27_5939_, lean_object* v_b_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_){
_start:
{
uint8_t v___x_173417__boxed_5944_; lean_object* v_res_5945_; 
v___x_173417__boxed_5944_ = lean_unbox(v___x_5937_);
v_res_5945_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173417__boxed_5944_, v_val_5938_, v_as_x27_5939_, v_b_5940_, v___y_5941_, v___y_5942_);
lean_dec_ref(v___y_5941_);
lean_dec(v_as_x27_5939_);
lean_dec_ref(v_val_5938_);
return v_res_5945_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_LeanExport_dumpExprAux(v_e_5946_, v_a_5947_, v_a_5948_);
lean_dec_ref(v_a_5947_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_LeanExport_dumpConstant(v_c_5951_, v_a_5952_, v_a_5953_);
lean_dec_ref(v_a_5952_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5956_, lean_object* v_as_5957_, lean_object* v_as_x27_5958_, lean_object* v_b_5959_, lean_object* v_a_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_){
_start:
{
lean_object* v___x_5964_; 
v___x_5964_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5956_, v_as_x27_5958_, v_b_5959_, v___y_5961_, v___y_5962_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5965_, lean_object* v_as_5966_, lean_object* v_as_x27_5967_, lean_object* v_b_5968_, lean_object* v_a_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
uint8_t v___x_177938__boxed_5973_; lean_object* v_res_5974_; 
v___x_177938__boxed_5973_ = lean_unbox(v___x_5965_);
v_res_5974_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_177938__boxed_5973_, v_as_5966_, v_as_x27_5967_, v_b_5968_, v_a_5969_, v___y_5970_, v___y_5971_);
lean_dec_ref(v___y_5970_);
lean_dec(v_as_x27_5967_);
lean_dec(v_as_5966_);
return v_res_5974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5975_, uint8_t v___x_5976_, lean_object* v_as_5977_, lean_object* v_as_x27_5978_, lean_object* v_b_5979_, lean_object* v_a_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_){
_start:
{
lean_object* v___x_5984_; 
v___x_5984_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5975_, v___x_5976_, v_as_x27_5978_, v_b_5979_, v___y_5981_, v___y_5982_);
return v___x_5984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5985_, lean_object* v___x_5986_, lean_object* v_as_5987_, lean_object* v_as_x27_5988_, lean_object* v_b_5989_, lean_object* v_a_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_){
_start:
{
uint8_t v___y_177955__boxed_5994_; uint8_t v___x_177956__boxed_5995_; lean_object* v_res_5996_; 
v___y_177955__boxed_5994_ = lean_unbox(v___y_5985_);
v___x_177956__boxed_5995_ = lean_unbox(v___x_5986_);
v_res_5996_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_177955__boxed_5994_, v___x_177956__boxed_5995_, v_as_5987_, v_as_x27_5988_, v_b_5989_, v_a_5990_, v___y_5991_, v___y_5992_);
lean_dec_ref(v___y_5991_);
lean_dec(v_as_x27_5988_);
lean_dec(v_as_5987_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5997_, lean_object* v_t_5998_, lean_object* v_k_5999_){
_start:
{
lean_object* v___x_6000_; 
v___x_6000_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5998_, v_k_5999_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_6001_, lean_object* v_t_6002_, lean_object* v_k_6003_){
_start:
{
lean_object* v_res_6004_; 
v_res_6004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_6001_, v_t_6002_, v_k_6003_);
lean_dec(v_k_6003_);
lean_dec(v_t_6002_);
return v_res_6004_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_6005_, lean_object* v_val_6006_, lean_object* v_as_6007_, lean_object* v_as_x27_6008_, lean_object* v_b_6009_, lean_object* v_a_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_){
_start:
{
lean_object* v___x_6014_; 
v___x_6014_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_6005_, v_val_6006_, v_as_x27_6008_, v_b_6009_, v___y_6011_, v___y_6012_);
return v___x_6014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_6015_, lean_object* v_val_6016_, lean_object* v_as_6017_, lean_object* v_as_x27_6018_, lean_object* v_b_6019_, lean_object* v_a_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
uint8_t v___x_177977__boxed_6024_; lean_object* v_res_6025_; 
v___x_177977__boxed_6024_ = lean_unbox(v___x_6015_);
v_res_6025_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_177977__boxed_6024_, v_val_6016_, v_as_6017_, v_as_x27_6018_, v_b_6019_, v_a_6020_, v___y_6021_, v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v_as_x27_6018_);
lean_dec(v_as_6017_);
lean_dec_ref(v_val_6016_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_6026_, lean_object* v_as_x27_6027_, lean_object* v_b_6028_, lean_object* v_a_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_){
_start:
{
lean_object* v___x_6033_; 
v___x_6033_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_6027_, v_b_6028_, v___y_6030_, v___y_6031_);
return v___x_6033_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_6034_, lean_object* v_as_x27_6035_, lean_object* v_b_6036_, lean_object* v_a_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_6034_, v_as_x27_6035_, v_b_6036_, v_a_6037_, v___y_6038_, v___y_6039_);
lean_dec_ref(v___y_6038_);
lean_dec(v_as_x27_6035_);
lean_dec(v_as_6034_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_6042_, lean_object* v_as_x27_6043_, lean_object* v_b_6044_, lean_object* v_a_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_){
_start:
{
lean_object* v___x_6049_; 
v___x_6049_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_6043_, v_b_6044_, v___y_6046_, v___y_6047_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_6050_, lean_object* v_as_x27_6051_, lean_object* v_b_6052_, lean_object* v_a_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v_res_6057_; 
v_res_6057_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_6050_, v_as_x27_6051_, v_b_6052_, v_a_6053_, v___y_6054_, v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v_as_x27_6051_);
lean_dec(v_as_6050_);
return v_res_6057_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = l_Lean_versionString;
v___x_6060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
return v___x_6060_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6061_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_6062_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_6061_);
return v___x_6063_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; 
v___x_6065_ = l_Lean_githash;
v___x_6066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
return v___x_6066_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6067_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_6068_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___x_6067_);
return v___x_6069_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6070_ = lean_box(0);
v___x_6071_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_6072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_6070_);
return v___x_6072_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6073_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_6074_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_6075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6074_);
lean_ctor_set(v___x_6075_, 1, v___x_6073_);
return v___x_6075_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_6076_; lean_object* v_leanMeta_6077_; 
v___x_6076_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_6077_ = l_Lean_Json_mkObj(v___x_6076_);
return v_leanMeta_6077_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_6096_; lean_object* v_exporterMeta_6097_; 
v___x_6096_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_6097_ = l_Lean_Json_mkObj(v___x_6096_);
return v_exporterMeta_6097_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_6098_; lean_object* v_formatMeta_6099_; 
v___x_6098_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_6099_ = l_Lean_Json_mkObj(v___x_6098_);
return v_formatMeta_6099_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; 
v_exporterMeta_6102_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_6103_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v_exporterMeta_6102_);
return v___x_6104_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; 
v_leanMeta_6106_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_6107_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_6108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v_leanMeta_6106_);
return v___x_6108_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v_formatMeta_6110_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_6111_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_6112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set(v___x_6112_, 1, v_formatMeta_6110_);
return v___x_6112_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = lean_box(0);
v___x_6114_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_6115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_6113_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6116_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_6117_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_6118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set(v___x_6118_, 1, v___x_6116_);
return v___x_6118_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6119_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_6120_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_6121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_6119_);
return v___x_6121_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; 
v___x_6122_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_6123_ = l_Lean_Json_mkObj(v___x_6122_);
return v___x_6123_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6124_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_6125_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_6126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
lean_ctor_set(v___x_6126_, 1, v___x_6124_);
return v___x_6126_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6127_ = lean_box(0);
v___x_6128_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_6129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_6127_);
return v___x_6129_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6130_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_6131_ = l_Lean_Json_mkObj(v___x_6130_);
return v___x_6131_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_6132_; 
v___x_6132_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_6132_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; 
v___x_6133_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_6134_ = l_Lean_Json_compress(v___x_6133_);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_6135_){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6137_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_6138_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_6137_);
if (lean_obj_tag(v___x_6138_) == 0)
{
lean_object* v_a_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6147_; 
v_a_6139_ = lean_ctor_get(v___x_6138_, 0);
v_isSharedCheck_6147_ = !lean_is_exclusive(v___x_6138_);
if (v_isSharedCheck_6147_ == 0)
{
v___x_6141_ = v___x_6138_;
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_a_6139_);
lean_dec(v___x_6138_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6143_; lean_object* v___x_6145_; 
v___x_6143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6143_, 0, v_a_6139_);
lean_ctor_set(v___x_6143_, 1, v_a_6135_);
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 0, v___x_6143_);
v___x_6145_ = v___x_6141_;
goto v_reusejp_6144_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v___x_6143_);
v___x_6145_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6144_;
}
v_reusejp_6144_:
{
return v___x_6145_;
}
}
}
else
{
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6155_; 
lean_dec_ref(v_a_6135_);
v_a_6148_ = lean_ctor_get(v___x_6138_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___x_6138_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6150_ = v___x_6138_;
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___x_6138_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6153_; 
if (v_isShared_6151_ == 0)
{
v___x_6153_ = v___x_6150_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
v___x_6153_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
return v___x_6153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_6156_, lean_object* v_a_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l_LeanExport_dumpMetadata___redArg(v_a_6156_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_6159_, lean_object* v_a_6160_){
_start:
{
lean_object* v___x_6162_; 
v___x_6162_ = l_LeanExport_dumpMetadata___redArg(v_a_6160_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l_LeanExport_dumpMetadata(v_a_6163_, v_a_6164_);
lean_dec_ref(v_a_6163_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object* v_as_x27_6167_, lean_object* v_b_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_){
_start:
{
if (lean_obj_tag(v_as_x27_6167_) == 0)
{
lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6172_, 0, v_b_6168_);
lean_ctor_set(v___x_6172_, 1, v___y_6170_);
v___x_6173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
return v___x_6173_;
}
else
{
lean_object* v_head_6174_; lean_object* v_tail_6175_; lean_object* v_visitedNames_6176_; lean_object* v_visitedLevels_6177_; lean_object* v_visitedExprs_6178_; lean_object* v_visitedConstants_6179_; uint8_t v_exportMData_6180_; uint8_t v_exportUnsafe_6181_; uint8_t v_ignoreMissing_6182_; lean_object* v_recursorMap_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6196_; 
v_head_6174_ = lean_ctor_get(v_as_x27_6167_, 0);
v_tail_6175_ = lean_ctor_get(v_as_x27_6167_, 1);
v_visitedNames_6176_ = lean_ctor_get(v___y_6170_, 0);
v_visitedLevels_6177_ = lean_ctor_get(v___y_6170_, 1);
v_visitedExprs_6178_ = lean_ctor_get(v___y_6170_, 2);
v_visitedConstants_6179_ = lean_ctor_get(v___y_6170_, 3);
v_exportMData_6180_ = lean_ctor_get_uint8(v___y_6170_, sizeof(void*)*6);
v_exportUnsafe_6181_ = lean_ctor_get_uint8(v___y_6170_, sizeof(void*)*6 + 1);
v_ignoreMissing_6182_ = lean_ctor_get_uint8(v___y_6170_, sizeof(void*)*6 + 2);
v_recursorMap_6183_ = lean_ctor_get(v___y_6170_, 5);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___y_6170_);
if (v_isSharedCheck_6196_ == 0)
{
lean_object* v_unused_6197_; 
v_unused_6197_ = lean_ctor_get(v___y_6170_, 4);
lean_dec(v_unused_6197_);
v___x_6185_ = v___y_6170_;
v_isShared_6186_ = v_isSharedCheck_6196_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_recursorMap_6183_);
lean_inc(v_visitedConstants_6179_);
lean_inc(v_visitedExprs_6178_);
lean_inc(v_visitedLevels_6177_);
lean_inc(v_visitedNames_6176_);
lean_dec(v___y_6170_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6196_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6190_; 
v___x_6187_ = lean_box(0);
v___x_6188_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_6186_ == 0)
{
lean_ctor_set(v___x_6185_, 4, v___x_6188_);
v___x_6190_ = v___x_6185_;
goto v_reusejp_6189_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_visitedNames_6176_);
lean_ctor_set(v_reuseFailAlloc_6195_, 1, v_visitedLevels_6177_);
lean_ctor_set(v_reuseFailAlloc_6195_, 2, v_visitedExprs_6178_);
lean_ctor_set(v_reuseFailAlloc_6195_, 3, v_visitedConstants_6179_);
lean_ctor_set(v_reuseFailAlloc_6195_, 4, v___x_6188_);
lean_ctor_set(v_reuseFailAlloc_6195_, 5, v_recursorMap_6183_);
lean_ctor_set_uint8(v_reuseFailAlloc_6195_, sizeof(void*)*6, v_exportMData_6180_);
lean_ctor_set_uint8(v_reuseFailAlloc_6195_, sizeof(void*)*6 + 1, v_exportUnsafe_6181_);
lean_ctor_set_uint8(v_reuseFailAlloc_6195_, sizeof(void*)*6 + 2, v_ignoreMissing_6182_);
v___x_6190_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6189_;
}
v_reusejp_6189_:
{
lean_object* v___x_6191_; 
lean_inc(v_head_6174_);
v___x_6191_ = l_LeanExport_dumpConstant(v_head_6174_, v___y_6169_, v___x_6190_);
if (lean_obj_tag(v___x_6191_) == 0)
{
lean_object* v_a_6192_; lean_object* v_snd_6193_; 
v_a_6192_ = lean_ctor_get(v___x_6191_, 0);
lean_inc(v_a_6192_);
lean_dec_ref_known(v___x_6191_, 1);
v_snd_6193_ = lean_ctor_get(v_a_6192_, 1);
lean_inc(v_snd_6193_);
lean_dec(v_a_6192_);
v_as_x27_6167_ = v_tail_6175_;
v_b_6168_ = v___x_6187_;
v___y_6170_ = v_snd_6193_;
goto _start;
}
else
{
return v___x_6191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object* v_as_x27_6198_, lean_object* v_b_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6198_, v_b_6199_, v___y_6200_, v___y_6201_);
lean_dec_ref(v___y_6200_);
lean_dec(v_as_x27_6198_);
return v_res_6203_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object* v_env_6204_, lean_object* v_cliOptions_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = l_LeanExport_initState(v_env_6204_, v_cliOptions_6205_, v___y_6207_, v___y_6208_);
if (lean_obj_tag(v___x_6210_) == 0)
{
lean_object* v_a_6211_; lean_object* v_snd_6212_; lean_object* v___x_6213_; 
v_a_6211_ = lean_ctor_get(v___x_6210_, 0);
lean_inc(v_a_6211_);
lean_dec_ref_known(v___x_6210_, 1);
v_snd_6212_ = lean_ctor_get(v_a_6211_, 1);
lean_inc(v_snd_6212_);
lean_dec(v_a_6211_);
v___x_6213_ = l_LeanExport_dumpMetadata___redArg(v_snd_6212_);
if (lean_obj_tag(v___x_6213_) == 0)
{
lean_object* v_a_6214_; lean_object* v_snd_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; 
v_a_6214_ = lean_ctor_get(v___x_6213_, 0);
lean_inc(v_a_6214_);
lean_dec_ref_known(v___x_6213_, 1);
v_snd_6215_ = lean_ctor_get(v_a_6214_, 1);
lean_inc(v_snd_6215_);
lean_dec(v_a_6214_);
v___x_6216_ = lean_box(0);
v___x_6217_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v___y_6206_, v___x_6216_, v___y_6207_, v_snd_6215_);
if (lean_obj_tag(v___x_6217_) == 0)
{
lean_object* v_a_6218_; lean_object* v___x_6220_; uint8_t v_isShared_6221_; uint8_t v_isSharedCheck_6234_; 
v_a_6218_ = lean_ctor_get(v___x_6217_, 0);
v_isSharedCheck_6234_ = !lean_is_exclusive(v___x_6217_);
if (v_isSharedCheck_6234_ == 0)
{
v___x_6220_ = v___x_6217_;
v_isShared_6221_ = v_isSharedCheck_6234_;
goto v_resetjp_6219_;
}
else
{
lean_inc(v_a_6218_);
lean_dec(v___x_6217_);
v___x_6220_ = lean_box(0);
v_isShared_6221_ = v_isSharedCheck_6234_;
goto v_resetjp_6219_;
}
v_resetjp_6219_:
{
lean_object* v_snd_6222_; lean_object* v___x_6224_; uint8_t v_isShared_6225_; uint8_t v_isSharedCheck_6232_; 
v_snd_6222_ = lean_ctor_get(v_a_6218_, 1);
v_isSharedCheck_6232_ = !lean_is_exclusive(v_a_6218_);
if (v_isSharedCheck_6232_ == 0)
{
lean_object* v_unused_6233_; 
v_unused_6233_ = lean_ctor_get(v_a_6218_, 0);
lean_dec(v_unused_6233_);
v___x_6224_ = v_a_6218_;
v_isShared_6225_ = v_isSharedCheck_6232_;
goto v_resetjp_6223_;
}
else
{
lean_inc(v_snd_6222_);
lean_dec(v_a_6218_);
v___x_6224_ = lean_box(0);
v_isShared_6225_ = v_isSharedCheck_6232_;
goto v_resetjp_6223_;
}
v_resetjp_6223_:
{
lean_object* v___x_6227_; 
if (v_isShared_6225_ == 0)
{
lean_ctor_set(v___x_6224_, 0, v___x_6216_);
v___x_6227_ = v___x_6224_;
goto v_reusejp_6226_;
}
else
{
lean_object* v_reuseFailAlloc_6231_; 
v_reuseFailAlloc_6231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6231_, 0, v___x_6216_);
lean_ctor_set(v_reuseFailAlloc_6231_, 1, v_snd_6222_);
v___x_6227_ = v_reuseFailAlloc_6231_;
goto v_reusejp_6226_;
}
v_reusejp_6226_:
{
lean_object* v___x_6229_; 
if (v_isShared_6221_ == 0)
{
lean_ctor_set(v___x_6220_, 0, v___x_6227_);
v___x_6229_ = v___x_6220_;
goto v_reusejp_6228_;
}
else
{
lean_object* v_reuseFailAlloc_6230_; 
v_reuseFailAlloc_6230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6230_, 0, v___x_6227_);
v___x_6229_ = v_reuseFailAlloc_6230_;
goto v_reusejp_6228_;
}
v_reusejp_6228_:
{
return v___x_6229_;
}
}
}
}
}
else
{
return v___x_6217_;
}
}
else
{
return v___x_6213_;
}
}
else
{
return v___x_6210_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object* v_env_6235_, lean_object* v_cliOptions_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_){
_start:
{
lean_object* v_res_6241_; 
v_res_6241_ = l_LeanExport_dumpEnv___lam__0(v_env_6235_, v_cliOptions_6236_, v___y_6237_, v___y_6238_, v___y_6239_);
lean_dec_ref(v___y_6238_);
lean_dec(v___y_6237_);
lean_dec(v_cliOptions_6236_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object* v_a_6242_, lean_object* v_a_6243_){
_start:
{
if (lean_obj_tag(v_a_6242_) == 0)
{
lean_object* v___x_6244_; 
v___x_6244_ = l_List_reverse___redArg(v_a_6243_);
return v___x_6244_;
}
else
{
lean_object* v_head_6245_; lean_object* v_tail_6246_; lean_object* v___x_6248_; uint8_t v_isShared_6249_; uint8_t v_isSharedCheck_6256_; 
v_head_6245_ = lean_ctor_get(v_a_6242_, 0);
v_tail_6246_ = lean_ctor_get(v_a_6242_, 1);
v_isSharedCheck_6256_ = !lean_is_exclusive(v_a_6242_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6248_ = v_a_6242_;
v_isShared_6249_ = v_isSharedCheck_6256_;
goto v_resetjp_6247_;
}
else
{
lean_inc(v_tail_6246_);
lean_inc(v_head_6245_);
lean_dec(v_a_6242_);
v___x_6248_ = lean_box(0);
v_isShared_6249_ = v_isSharedCheck_6256_;
goto v_resetjp_6247_;
}
v_resetjp_6247_:
{
uint8_t v___x_6250_; 
v___x_6250_ = l_Lean_Name_isInternal(v_head_6245_);
if (v___x_6250_ == 0)
{
lean_object* v___x_6252_; 
if (v_isShared_6249_ == 0)
{
lean_ctor_set(v___x_6248_, 1, v_a_6243_);
v___x_6252_ = v___x_6248_;
goto v_reusejp_6251_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_head_6245_);
lean_ctor_set(v_reuseFailAlloc_6254_, 1, v_a_6243_);
v___x_6252_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6251_;
}
v_reusejp_6251_:
{
v_a_6242_ = v_tail_6246_;
v_a_6243_ = v___x_6252_;
goto _start;
}
}
else
{
lean_del_object(v___x_6248_);
lean_dec(v_head_6245_);
v_a_6242_ = v_tail_6246_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__1(lean_object* v_a_6257_, lean_object* v_a_6258_){
_start:
{
if (lean_obj_tag(v_a_6257_) == 0)
{
lean_object* v___x_6259_; 
v___x_6259_ = l_List_reverse___redArg(v_a_6258_);
return v___x_6259_;
}
else
{
lean_object* v_head_6260_; lean_object* v_tail_6261_; lean_object* v___x_6263_; uint8_t v_isShared_6264_; uint8_t v_isSharedCheck_6270_; 
v_head_6260_ = lean_ctor_get(v_a_6257_, 0);
v_tail_6261_ = lean_ctor_get(v_a_6257_, 1);
v_isSharedCheck_6270_ = !lean_is_exclusive(v_a_6257_);
if (v_isSharedCheck_6270_ == 0)
{
v___x_6263_ = v_a_6257_;
v_isShared_6264_ = v_isSharedCheck_6270_;
goto v_resetjp_6262_;
}
else
{
lean_inc(v_tail_6261_);
lean_inc(v_head_6260_);
lean_dec(v_a_6257_);
v___x_6263_ = lean_box(0);
v_isShared_6264_ = v_isSharedCheck_6270_;
goto v_resetjp_6262_;
}
v_resetjp_6262_:
{
lean_object* v_fst_6265_; lean_object* v___x_6267_; 
v_fst_6265_ = lean_ctor_get(v_head_6260_, 0);
lean_inc(v_fst_6265_);
lean_dec(v_head_6260_);
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 1, v_a_6258_);
lean_ctor_set(v___x_6263_, 0, v_fst_6265_);
v___x_6267_ = v___x_6263_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_fst_6265_);
lean_ctor_set(v_reuseFailAlloc_6269_, 1, v_a_6258_);
v___x_6267_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
v_a_6257_ = v_tail_6261_;
v_a_6258_ = v___x_6267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object* v_env_6271_, lean_object* v_constants_x3f_6272_, lean_object* v_cliOptions_6273_){
_start:
{
lean_object* v___y_6276_; 
if (lean_obj_tag(v_constants_x3f_6272_) == 0)
{
lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; 
lean_inc_ref(v_env_6271_);
v___x_6279_ = l_Lean_Environment_constants(v_env_6271_);
v___x_6280_ = l_Lean_ConstMap_toList(v___x_6279_);
v___x_6281_ = lean_box(0);
v___x_6282_ = l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__1(v___x_6280_, v___x_6281_);
v___x_6283_ = l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__2(v___x_6282_, v___x_6281_);
v___y_6276_ = v___x_6283_;
goto v___jp_6275_;
}
else
{
lean_object* v_val_6284_; 
v_val_6284_ = lean_ctor_get(v_constants_x3f_6272_, 0);
lean_inc(v_val_6284_);
lean_dec_ref_known(v_constants_x3f_6272_, 1);
v___y_6276_ = v_val_6284_;
goto v___jp_6275_;
}
v___jp_6275_:
{
lean_object* v___f_6277_; lean_object* v___x_6278_; 
lean_inc_ref(v_env_6271_);
v___f_6277_ = lean_alloc_closure((void*)(l_LeanExport_dumpEnv___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6277_, 0, v_env_6271_);
lean_closure_set(v___f_6277_, 1, v_cliOptions_6273_);
lean_closure_set(v___f_6277_, 2, v___y_6276_);
v___x_6278_ = l_LeanExport_M_run___redArg(v_env_6271_, v___f_6277_);
return v___x_6278_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object* v_env_6285_, lean_object* v_constants_x3f_6286_, lean_object* v_cliOptions_6287_, lean_object* v_a_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_LeanExport_dumpEnv(v_env_6285_, v_constants_x3f_6286_, v_cliOptions_6287_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object* v_as_6290_, lean_object* v_as_x27_6291_, lean_object* v_b_6292_, lean_object* v_a_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_){
_start:
{
lean_object* v___x_6297_; 
v___x_6297_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6291_, v_b_6292_, v___y_6294_, v___y_6295_);
return v___x_6297_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object* v_as_6298_, lean_object* v_as_x27_6299_, lean_object* v_b_6300_, lean_object* v_a_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v_res_6305_; 
v_res_6305_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6298_, v_as_x27_6299_, v_b_6300_, v_a_6301_, v___y_6302_, v___y_6303_);
lean_dec_ref(v___y_6302_);
lean_dec(v_as_x27_6299_);
lean_dec(v_as_6298_);
return v_res_6305_;
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

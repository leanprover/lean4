// Lean compiler output
// Module: Lean.Meta.Tactic.ElimInfo
// Imports: public import Lean.Meta.Check import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprElimAltInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declName\?"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "provesMotive"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17;
static const lean_string_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprElimAltInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprElimAltInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprElimAltInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprElimAltInfo = (const lean_object*)&l_Lean_Meta_instReprElimAltInfo___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedElimAltInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedElimAltInfo = (const lean_object*)&l_Lean_Meta_instInhabitedElimAltInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimExpr"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimType"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "motivePos"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "targetsPos"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "altsInfo"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "numComplexMotiveArgs"};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprElimInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprElimInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprElimInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprElimInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprElimInfo = (const lean_object*)&l_Lean_Meta_instReprElimInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__2;
static const lean_array_object l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__3 = (const lean_object*)&l_Lean_Meta_instInhabitedElimInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedElimInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Motive result type must be a sort, not"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Expected "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " parameters at motive type, got "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Unexpected eliminator type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0_value;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "Expected resulting type of eliminator to be an application of one of its parameters (the motive), but found"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__0 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__1 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value;
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 113, 55, 104, 212, 17, 5, 40)}};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__2 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__2_value;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__3 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__3_value;
static const lean_ctor_object l_Lean_Meta_getElimExprInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__4 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__4_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__5;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eliminator"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__6 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__6_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__7;
static const lean_string_object l_Lean_Meta_getElimExprInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l_Lean_Meta_getElimExprInfo___closed__8 = (const lean_object*)&l_Lean_Meta_getElimExprInfo___closed__8_value;
static lean_once_cell_t l_Lean_Meta_getElimExprInfo___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getElimExprInfo___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Invalid target:"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Insufficient number of targets for `"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Too many targets for `"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to infer implicit target"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Failed to infer implicit target `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_addImplicitTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_addImplicitTargets___closed__0 = (const lean_object*)&l_Lean_Meta_addImplicitTargets___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCustomEliminator_default = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCustomEliminator = (const lean_object*)&l_Lean_Meta_instInhabitedCustomEliminator_default___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object*);
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_getElimExprInfo___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__1_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "typeNames"};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__3_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimName"};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCustomEliminator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCustomEliminator_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCustomEliminator___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCustomEliminator = (const lean_object*)&l_Lean_Meta_instReprCustomEliminator___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSMap"};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCustomEliminators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCustomEliminators_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCustomEliminators___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCustomEliminators = (const lean_object*)&l_Lean_Meta_instReprCustomEliminators___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "customEliminatorExt"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 136, 153, 60, 178, 181, 251, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addCustomEliminatorEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_customEliminatorExt;
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Unexpected eliminator target type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ElimInfo"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 23, 41, 18, 182, 163, 163, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(97, 22, 214, 90, 248, 223, 62, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 37, 80, 174, 60, 227, 242, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 131, 121, 207, 209, 142, 148, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 30, 84, 209, 139, 131, 70, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 186, 117, 126, 128, 87, 152, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 106, 250, 33, 19, 38, 14, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 152, 58, 59, 147, 212, 205, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 67, 101, 228, 115, 139, 239, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 154, 76, 162, 203, 145, 140, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "induction_eliminator"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 48, 244, 108, 60, 232, 79, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "custom `rec`-like eliminator for the `induction` tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 849, .m_capacity = 849, .m_length = 792, .m_data = "Registers a custom eliminator for the `induction` tactic.\n\nWhenever the types of the targets in an `induction` call matches a custom eliminator, it is used\ninstead of the recursor. This can be useful for redefining the default eliminator to a more useful\none.\n\nExample:\n```lean example\nstructure Three where\n  val : Fin 3\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  induction x\n  -- val : Fin 3 ⊢ p ⟨val⟩\n\n@[induction_eliminator, elab_as_elim]\ndef Three.myRec {motive : Three → Sort u}\n    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :\n    ∀ x, motive x\n  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  induction x\n  -- ⊢ p ⟨0⟩\n  -- ⊢ p ⟨1⟩\n  -- ⊢ p ⟨2⟩\n```\n\n`@[cases_eliminator]` works similarly for the `cases` tactic.\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),((lean_object*)(((size_t)(913872705) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 209, 182, 172, 157, 111, 193, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 254, 161, 0, 64, 194, 151, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 62, 167, 93, 244, 208, 254, 35)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(42, 73, 103, 197, 19, 167, 228, 154)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cases_eliminator"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 14, 239, 189, 147, 54, 173, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "custom `casesOn`-like eliminator for the `cases` tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 849, .m_capacity = 849, .m_length = 792, .m_data = "Registers a custom eliminator for the `cases` tactic.\n\nWhenever the types of the targets in an `cases` call matches a custom eliminator, it is used\ninstead of the `casesOn` eliminator. This can be useful for redefining the default eliminator to a\nmore useful one.\n\nExample:\n```lean example\nstructure Three where\n  val : Fin 3\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  cases x\n  -- val : Fin 3 ⊢ p ⟨val⟩\n\n@[cases_eliminator, elab_as_elim]\ndef Three.myRec {motive : Three → Sort u}\n    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :\n    ∀ x, motive x\n  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two\n\nexample (x : Three) (p : Three → Prop) : p x := by\n  cases x\n  -- ⊢ p ⟨0⟩\n  -- ⊢ p ⟨1⟩\n  -- ⊢ p ⟨2⟩\n```\n\n`@[induction_eliminator]` works similarly for the `induction` tactic.\n"};
static const lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_getCustomEliminator_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_addImplicitTargets___closed__0_value)}};
static const lean_object* l_Lean_Meta_getCustomEliminator_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_getCustomEliminator_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__1));
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_val_10_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_val_10_);
lean_dec_ref_known(v_x_7_, 1);
v___x_11_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___closed__3));
v___x_12_ = lean_unsigned_to_nat(1024u);
v___x_13_ = l_Lean_Name_reprPrec(v_val_10_, v___x_12_);
v___x_14_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_11_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = l_Repr_addAppParen(v___x_14_, v_x_8_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(v_x_16_, v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprElimAltInfo_repr_spec__1(lean_object* v_a_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_nat_to_int(v_a_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(13u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(16u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__0));
v___x_54_ = lean_string_length(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__19);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___redArg(lean_object* v_x_61_){
_start:
{
lean_object* v_name_62_; lean_object* v_declName_x3f_63_; lean_object* v_numFields_64_; uint8_t v_provesMotive_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_name_62_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_name_62_);
v_declName_x3f_63_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_declName_x3f_63_);
v_numFields_64_ = lean_ctor_get(v_x_61_, 2);
lean_inc(v_numFields_64_);
v_provesMotive_65_ = lean_ctor_get_uint8(v_x_61_, sizeof(void*)*3);
lean_dec_ref(v_x_61_);
v___x_66_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_67_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__6));
v___x_68_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__7);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l_Lean_Name_reprPrec(v_name_62_, v___x_69_);
v___x_71_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_68_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = 0;
v___x_73_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_67_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_box(1);
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__11));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_66_);
v___x_82_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_83_ = l_Option_repr___at___00Lean_Meta_instReprElimAltInfo_repr_spec__0(v_declName_x3f_63_, v___x_69_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_72_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_75_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_77_);
v___x_89_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__14));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_66_);
v___x_92_ = l_Nat_reprFast(v_numFields_64_);
v___x_93_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_82_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_72_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_75_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_77_);
v___x_99_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__16));
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_66_);
v___x_102_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__17);
v___x_103_ = l_Bool_repr___redArg(v_provesMotive_65_);
v___x_104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_72_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_108_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_106_);
v___x_110_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_72_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr(lean_object* v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_instReprElimAltInfo_repr(v_x_117_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_dec(v_x_129_);
return v_x_130_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_144_; 
v_head_132_ = lean_ctor_get(v_x_131_, 0);
v_tail_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_144_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_head_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
lean_inc(v_x_129_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 5);
lean_ctor_set(v___x_135_, 1, v_x_129_);
lean_ctor_set(v___x_135_, 0, v_x_130_);
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_x_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_x_129_);
v___x_138_ = v_reuseFailAlloc_143_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = l_Nat_reprFast(v_head_132_);
v___x_140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v_x_130_ = v___x_141_;
v_x_131_ = v_tail_133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_dec(v_x_145_);
return v_x_146_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_head_148_ = lean_ctor_get(v_x_147_, 0);
v_tail_149_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v_x_147_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_tail_149_);
lean_inc(v_head_148_);
lean_dec(v_x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
lean_inc(v_x_145_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 5);
lean_ctor_set(v___x_151_, 1, v_x_145_);
lean_ctor_set(v___x_151_, 0, v_x_146_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_x_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_x_145_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = l_Nat_reprFast(v_head_148_);
v___x_156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1_spec__3(v_x_145_, v___x_157_, v_tail_149_);
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Nat_reprFast(v___y_161_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_166_; 
lean_dec(v_x_165_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_tail_167_; 
v_tail_167_ = lean_ctor_get(v_x_164_, 1);
if (lean_obj_tag(v_tail_167_) == 0)
{
lean_object* v_head_168_; lean_object* v___x_169_; 
lean_dec(v_x_165_);
v_head_168_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_168_);
lean_dec_ref_known(v_x_164_, 2);
v___x_169_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_168_);
return v___x_169_;
}
else
{
lean_object* v_head_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_tail_167_);
v_head_170_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_170_);
lean_dec_ref_known(v_x_164_, 2);
v___x_171_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0___lam__0(v_head_170_);
v___x_172_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0_spec__1(v_x_165_, v___x_171_, v_tail_167_);
return v___x_172_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__0));
v___x_179_ = lean_string_length(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__3);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(lean_object* v_xs_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_array_get_size(v_xs_189_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_nat_dec_eq(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_193_ = lean_array_to_list(v_xs_189_);
v___x_194_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_195_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0_spec__0(v___x_193_, v___x_194_);
v___x_196_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_197_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_195_);
v___x_199_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_196_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Std_Format_fill(v___x_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_xs_189_);
v___x_203_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_dec(v_x_204_);
return v_x_205_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_head_207_ = lean_ctor_get(v_x_206_, 0);
v_tail_208_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v_x_206_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_head_207_);
lean_dec(v_x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
lean_inc(v_x_204_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 5);
lean_ctor_set(v___x_210_, 1, v_x_204_);
lean_ctor_set(v___x_210_, 0, v_x_205_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_x_204_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_207_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v_x_205_ = v___x_215_;
v_x_206_ = v_tail_208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_dec(v_x_219_);
return v_x_220_;
}
else
{
lean_object* v_head_222_; lean_object* v_tail_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_head_222_ = lean_ctor_get(v_x_221_, 0);
v_tail_223_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v_x_221_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_tail_223_);
lean_inc(v_head_222_);
lean_dec(v_x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
lean_inc(v_x_219_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 5);
lean_ctor_set(v___x_225_, 1, v_x_219_);
lean_ctor_set(v___x_225_, 0, v_x_220_);
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_x_220_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_x_219_);
v___x_228_ = v_reuseFailAlloc_232_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_222_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4_spec__6(v_x_219_, v___x_230_, v_tail_223_);
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v___x_236_; 
lean_dec(v_x_235_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v_tail_237_; 
v_tail_237_ = lean_ctor_get(v_x_234_, 1);
if (lean_obj_tag(v_tail_237_) == 0)
{
lean_object* v_head_238_; lean_object* v___x_239_; 
lean_dec(v_x_235_);
v_head_238_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_238_);
lean_dec_ref_known(v_x_234_, 2);
v___x_239_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_238_);
return v___x_239_;
}
else
{
lean_object* v_head_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_tail_237_);
v_head_240_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_240_);
lean_dec_ref_known(v_x_234_, 2);
v___x_241_ = l_Lean_Meta_instReprElimAltInfo_repr___redArg(v_head_240_);
v___x_242_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2_spec__4(v_x_235_, v___x_241_, v_tail_237_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(lean_object* v_xs_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_array_get_size(v_xs_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_247_ = lean_array_to_list(v_xs_243_);
v___x_248_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_249_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1_spec__2(v___x_247_, v___x_248_);
v___x_250_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_251_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_249_);
v___x_253_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_250_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Std_Format_fill(v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
lean_dec_ref(v_xs_243_);
v___x_257_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_257_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(12u);
v___x_268_ = lean_nat_to_int(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(14u);
v___x_279_ = lean_nat_to_int(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(24u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___redArg(lean_object* v_x_288_){
_start:
{
lean_object* v_elimExpr_289_; lean_object* v_elimType_290_; lean_object* v_motivePos_291_; lean_object* v_targetsPos_292_; lean_object* v_altsInfo_293_; lean_object* v_numComplexMotiveArgs_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_elimExpr_289_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_elimExpr_289_);
v_elimType_290_ = lean_ctor_get(v_x_288_, 1);
lean_inc_ref(v_elimType_290_);
v_motivePos_291_ = lean_ctor_get(v_x_288_, 2);
lean_inc(v_motivePos_291_);
v_targetsPos_292_ = lean_ctor_get(v_x_288_, 3);
lean_inc_ref(v_targetsPos_292_);
v_altsInfo_293_ = lean_ctor_get(v_x_288_, 4);
lean_inc_ref(v_altsInfo_293_);
v_numComplexMotiveArgs_294_ = lean_ctor_get(v_x_288_, 5);
lean_inc(v_numComplexMotiveArgs_294_);
lean_dec_ref(v_x_288_);
v___x_295_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_296_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__3));
v___x_297_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Lean_instReprExpr_repr(v_elimExpr_289_, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = 0;
v___x_302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_301_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_296_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_box(1);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__6));
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_295_);
v___x_311_ = l_Lean_instReprExpr_repr(v_elimType_290_, v___x_298_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_297_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_301_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_310_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_304_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_306_);
v___x_317_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__8));
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_295_);
v___x_320_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_321_ = l_Nat_reprFast(v_motivePos_291_);
v___x_322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_301_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_319_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_304_);
v___x_327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_306_);
v___x_328_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__10));
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_295_);
v___x_331_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__11);
v___x_332_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0(v_targetsPos_292_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_301_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_330_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_304_);
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_306_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__13));
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_295_);
v___x_341_ = l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__1(v_altsInfo_293_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_297_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*1, v___x_301_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_304_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_306_);
v___x_347_ = ((lean_object*)(l_Lean_Meta_instReprElimInfo_repr___redArg___closed__15));
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_295_);
v___x_350_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__16);
v___x_351_ = l_Nat_reprFast(v_numComplexMotiveArgs_294_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_301_);
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_349_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_357_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_355_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_356_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*1, v___x_301_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr(lean_object* v_x_363_, lean_object* v_prec_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_instReprElimInfo_repr___redArg(v_x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo_repr___boxed(lean_object* v_x_366_, lean_object* v_prec_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_instReprElimInfo_repr(v_x_366_, v_prec_367_);
lean_dec(v_prec_367_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_box(0);
v___x_375_ = ((lean_object*)(l_Lean_Meta_instInhabitedElimInfo_default___closed__1));
v___x_376_ = l_Lean_Expr_const___override(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = ((lean_object*)(l_Lean_Meta_instInhabitedElimInfo_default___closed__3));
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_obj_once(&l_Lean_Meta_instInhabitedElimInfo_default___closed__2, &l_Lean_Meta_instInhabitedElimInfo_default___closed__2_once, _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__2);
v___x_382_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_ctor_set(v___x_382_, 2, v___x_380_);
lean_ctor_set(v___x_382_, 3, v___x_379_);
lean_ctor_set(v___x_382_, 4, v___x_379_);
lean_ctor_set(v___x_382_, 5, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo_default(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_obj_once(&l_Lean_Meta_instInhabitedElimInfo_default___closed__4, &l_Lean_Meta_instInhabitedElimInfo_default___closed__4_once, _init_l_Lean_Meta_instInhabitedElimInfo_default___closed__4);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_instInhabitedElimInfo_default;
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object* v_motive_385_, lean_object* v_n_386_, lean_object* v_x_387_){
_start:
{
switch(lean_obj_tag(v_x_387_))
{
case 7:
{
lean_object* v_body_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_body_388_ = lean_ctor_get(v_x_387_, 2);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_n_386_, v___x_389_);
lean_dec(v_n_386_);
v_n_386_ = v___x_390_;
v_x_387_ = v_body_388_;
goto _start;
}
case 8:
{
lean_object* v_body_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_body_392_ = lean_ctor_get(v_x_387_, 3);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_n_386_, v___x_393_);
lean_dec(v_n_386_);
v_n_386_ = v___x_394_;
v_x_387_ = v_body_392_;
goto _start;
}
default: 
{
lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = l_Lean_Expr_getAppFn(v_x_387_);
v___x_397_ = lean_expr_eqv(v___x_396_, v_motive_385_);
lean_dec_ref(v___x_396_);
v___x_398_ = lean_box(v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_n_386_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object* v_motive_400_, lean_object* v_n_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_altArity(v_motive_400_, v_n_401_, v_x_402_);
lean_dec_ref(v_x_402_);
lean_dec_ref(v_motive_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(lean_object* v_k_404_, lean_object* v_b_405_, lean_object* v_c_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
v___x_412_ = lean_apply_7(v_k_404_, v_b_405_, v_c_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed(lean_object* v_k_413_, lean_object* v_b_414_, lean_object* v_c_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0(v_k_413_, v_b_414_, v_c_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(lean_object* v_type_422_, lean_object* v_k_423_, uint8_t v_cleanupAnnotations_424_, uint8_t v_whnfType_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; 
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_431_, 0, v_k_423_);
v___x_432_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_422_, v___f_431_, v_cleanupAnnotations_424_, v_whnfType_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
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
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
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
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg___boxed(lean_object* v_type_449_, lean_object* v_k_450_, lean_object* v_cleanupAnnotations_451_, lean_object* v_whnfType_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_458_; uint8_t v_whnfType_boxed_459_; lean_object* v_res_460_; 
v_cleanupAnnotations_boxed_458_ = lean_unbox(v_cleanupAnnotations_451_);
v_whnfType_boxed_459_ = lean_unbox(v_whnfType_452_);
v_res_460_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_type_449_, v_k_450_, v_cleanupAnnotations_boxed_458_, v_whnfType_boxed_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(lean_object* v_00_u03b1_461_, lean_object* v_type_462_, lean_object* v_k_463_, uint8_t v_cleanupAnnotations_464_, uint8_t v_whnfType_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_type_462_, v_k_463_, v_cleanupAnnotations_464_, v_whnfType_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___boxed(lean_object* v_00_u03b1_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v_cleanupAnnotations_475_, lean_object* v_whnfType_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_482_; uint8_t v_whnfType_boxed_483_; lean_object* v_res_484_; 
v_cleanupAnnotations_boxed_482_ = lean_unbox(v_cleanupAnnotations_475_);
v_whnfType_boxed_483_ = lean_unbox(v_whnfType_476_);
v_res_484_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2(v_00_u03b1_472_, v_type_473_, v_k_474_, v_cleanupAnnotations_boxed_482_, v_whnfType_boxed_483_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; lean_object* v___x_493_; lean_object* v_mctx_494_; lean_object* v_lctx_495_; lean_object* v_options_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_491_ = lean_st_ref_get(v___y_489_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = lean_st_ref_get(v___y_487_);
v_mctx_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_494_);
lean_dec(v___x_493_);
v_lctx_495_ = lean_ctor_get(v___y_486_, 2);
v_options_496_ = lean_ctor_get(v___y_488_, 2);
lean_inc_ref(v_options_496_);
lean_inc_ref(v_lctx_495_);
v___x_497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_497_, 0, v_env_492_);
lean_ctor_set(v___x_497_, 1, v_mctx_494_);
lean_ctor_set(v___x_497_, 2, v_lctx_495_);
lean_ctor_set(v___x_497_, 3, v_options_496_);
v___x_498_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_msgData_485_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2___boxed(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msgData_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_ref_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_ref_513_ = lean_ctor_get(v___y_510_, 5);
v___x_514_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_inc(v_ref_513_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_ref_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg___boxed(lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__0));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__2));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__4));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__6));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(lean_object* v_a_543_, lean_object* v_x_544_, lean_object* v_motiveParams_545_, lean_object* v_motiveResultType_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_array_get_size(v_motiveParams_545_);
v___x_561_ = lean_array_get_size(v_x_544_);
v___x_562_ = lean_nat_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_563_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__3);
v___x_564_ = l_Nat_reprFast(v___x_561_);
v___x_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = l_Lean_MessageData_ofFormat(v___x_565_);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__5);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Nat_reprFast(v___x_560_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = l_Lean_MessageData_ofFormat(v___x_571_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__7);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_indentExpr(v_a_543_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_577_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_578_;
}
else
{
goto v___jp_552_;
}
v___jp_552_:
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Expr_isSort(v_motiveResultType_546_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___closed__1);
v___x_555_ = l_Lean_indentExpr(v_a_543_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_556_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_a_543_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed(lean_object* v_a_579_, lean_object* v_x_580_, lean_object* v_motiveParams_581_, lean_object* v_motiveResultType_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0(v_a_579_, v_x_580_, v_motiveParams_581_, v_motiveResultType_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_motiveResultType_582_);
lean_dec_ref(v_motiveParams_581_);
lean_dec_ref(v_x_580_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(lean_object* v_xs_589_, lean_object* v_v_590_, lean_object* v_i_591_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_get_size(v_xs_589_);
v___x_593_ = lean_nat_dec_lt(v_i_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v_i_591_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_array_fget_borrowed(v_xs_589_, v_i_591_);
v___x_596_ = lean_expr_eqv(v___x_595_, v_v_590_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_i_591_, v___x_597_);
lean_dec(v_i_591_);
v_i_591_ = v___x_598_;
goto _start;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_i_591_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_601_, lean_object* v_v_602_, lean_object* v_i_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_601_, v_v_602_, v_i_603_);
lean_dec_ref(v_v_602_);
lean_dec_ref(v_xs_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object* v_xs_605_, lean_object* v_v_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__2(v_xs_605_, v_v_606_, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object* v_xs_609_, lean_object* v_v_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_609_, v_v_610_);
lean_dec_ref(v_v_610_);
lean_dec_ref(v_xs_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(lean_object* v_xs_612_, lean_object* v_v_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0_spec__0(v_xs_612_, v_v_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_val_616_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v___x_614_);
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
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object* v_xs_624_, lean_object* v_v_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_624_, v_v_625_);
lean_dec_ref(v_v_625_);
lean_dec_ref(v_xs_624_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__0));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(lean_object* v_xs_630_, lean_object* v_a_631_, size_t v_sz_632_, size_t v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_633_, v_sz_632_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_a_631_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_bs_634_);
return v___x_641_;
}
else
{
lean_object* v_v_642_; lean_object* v___x_643_; lean_object* v_bs_x27_644_; lean_object* v_a_646_; lean_object* v___x_651_; 
v_v_642_ = lean_array_uget(v_bs_634_, v_i_633_);
v___x_643_ = lean_unsigned_to_nat(0u);
v_bs_x27_644_ = lean_array_uset(v_bs_634_, v_i_633_, v___x_643_);
v___x_651_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_630_, v_v_642_);
lean_dec(v_v_642_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
lean_inc_ref(v_a_631_);
v___x_653_ = l_Lean_indentExpr(v_a_631_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_654_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v_a_646_ = v_a_656_;
goto v___jp_645_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_bs_x27_644_);
lean_dec_ref(v_a_631_);
v_a_657_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_651_, 1);
v_a_646_ = v_val_665_;
goto v___jp_645_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_633_, v___x_647_);
v___x_649_ = lean_array_uset(v_bs_x27_644_, v_i_633_, v_a_646_);
v_i_633_ = v___x_648_;
v_bs_634_ = v___x_649_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object* v_xs_666_, lean_object* v_a_667_, lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_bs_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_677_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_666_, v_a_667_, v_sz_boxed_676_, v_i_boxed_677_, v_bs_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v_xs_666_);
return v_res_678_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(lean_object* v_a_679_, lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
v___x_685_ = lean_expr_eqv(v_a_679_, v___x_684_);
if (v___x_685_ == 0)
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_681_, v___x_686_);
v_i_681_ = v___x_687_;
goto _start;
}
else
{
return v___x_685_;
}
}
else
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6___boxed(lean_object* v_a_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_stop_693_){
_start:
{
size_t v_i_boxed_694_; size_t v_stop_boxed_695_; uint8_t v_res_696_; lean_object* v_r_697_; 
v_i_boxed_694_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_stop_boxed_695_ = lean_unbox_usize(v_stop_693_);
lean_dec(v_stop_693_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_690_, v_as_691_, v_i_boxed_694_, v_stop_boxed_695_);
lean_dec_ref(v_as_691_);
lean_dec_ref(v_a_690_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(lean_object* v_as_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_array_get_size(v_as_698_);
v___x_702_ = lean_nat_dec_lt(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
return v___x_702_;
}
else
{
if (v___x_702_ == 0)
{
return v___x_702_;
}
else
{
size_t v___x_703_; size_t v___x_704_; uint8_t v___x_705_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_701_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4_spec__6(v_a_699_, v_as_698_, v___x_703_, v___x_704_);
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object* v_as_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v_as_706_, v_a_707_);
lean_dec_ref(v_a_707_);
lean_dec_ref(v_as_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(lean_object* v_upperBound_710_, lean_object* v_xs_711_, lean_object* v_motive_712_, lean_object* v___x_713_, lean_object* v_baseDeclName_x3f_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_a_723_; uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_lt(v_a_716_, v_upperBound_710_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v_baseDeclName_x3f_714_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_717_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_array_fget_borrowed(v_xs_711_, v_a_716_);
v___x_730_ = lean_expr_eqv(v___x_729_, v_motive_712_);
v___x_731_ = lean_bool_not(v___x_730_);
if (v___x_731_ == 0)
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
else
{
uint8_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v___x_713_, v___x_729_);
v___x_733_ = lean_bool_not(v___x_732_);
if (v___x_733_ == 0)
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Lean_Expr_fvarId_x21(v___x_729_);
v___x_735_ = l_Lean_FVarId_getDecl___redArg(v___x_734_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; uint8_t v___x_737_; uint8_t v___x_738_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_LocalDecl_binderInfo(v_a_736_);
v___x_738_ = l_Lean_BinderInfo_isExplicit(v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v_a_736_);
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_744_; lean_object* v___y_746_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Lean_LocalDecl_type(v_a_736_);
v___x_741_ = l_Lean_Meta_altArity(v_motive_712_, v___x_739_, v___x_740_);
lean_dec_ref(v___x_740_);
v_fst_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_fst_742_);
v_snd_743_ = lean_ctor_get(v___x_741_, 1);
lean_inc(v_snd_743_);
lean_dec_ref(v___x_741_);
v___x_744_ = l_Lean_LocalDecl_userName(v_a_736_);
lean_dec(v_a_736_);
if (lean_obj_tag(v_baseDeclName_x3f_714_) == 0)
{
v___y_746_ = v_baseDeclName_x3f_714_;
goto v___jp_745_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_val_750_ = lean_ctor_get(v_baseDeclName_x3f_714_, 0);
lean_inc(v___x_744_);
lean_inc(v_val_750_);
v___x_751_ = l_Lean_Name_append(v_val_750_, v___x_744_);
lean_inc(v___x_751_);
lean_inc_ref(v___x_715_);
v___x_752_ = l_Lean_Environment_contains(v___x_715_, v___x_751_, v___x_731_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v___x_751_);
v___x_753_ = lean_box(0);
v___y_746_ = v___x_753_;
goto v___jp_745_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_751_);
v___y_746_ = v___x_754_;
goto v___jp_745_;
}
}
v___jp_745_:
{
lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_747_, 0, v___x_744_);
lean_ctor_set(v___x_747_, 1, v___y_746_);
lean_ctor_set(v___x_747_, 2, v_fst_742_);
v___x_748_ = lean_unbox(v_snd_743_);
lean_dec(v_snd_743_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*3, v___x_748_);
v___x_749_ = lean_array_push(v_b_717_, v___x_747_);
v_a_723_ = v___x_749_;
goto v___jp_722_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref(v_b_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v_baseDeclName_x3f_714_);
v_a_755_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_735_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_735_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_a_716_, v___x_724_);
lean_dec(v_a_716_);
v_a_716_ = v___x_725_;
v_b_717_ = v_a_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object* v_upperBound_763_, lean_object* v_xs_764_, lean_object* v_motive_765_, lean_object* v___x_766_, lean_object* v_baseDeclName_x3f_767_, lean_object* v___x_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_763_, v_xs_764_, v_motive_765_, v___x_766_, v_baseDeclName_x3f_767_, v___x_768_, v_a_769_, v_b_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v___x_766_);
lean_dec_ref(v_motive_765_);
lean_dec_ref(v_xs_764_);
lean_dec(v_upperBound_763_);
return v_res_775_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object* v_xs_782_, lean_object* v_a_783_, lean_object* v_elimExpr_784_, lean_object* v_baseDeclName_x3f_785_, lean_object* v_type_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; 
if (lean_obj_tag(v_x_787_) == 5)
{
lean_object* v_fn_870_; lean_object* v_arg_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_fn_870_ = lean_ctor_get(v_x_787_, 0);
lean_inc_ref(v_fn_870_);
v_arg_871_ = lean_ctor_get(v_x_787_, 1);
lean_inc_ref(v_arg_871_);
lean_dec_ref_known(v_x_787_, 2);
v___x_872_ = lean_array_set(v_x_788_, v_x_789_, v_arg_871_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_sub(v_x_789_, v___x_873_);
lean_dec(v_x_789_);
v_x_787_ = v_fn_870_;
v_x_788_ = v___x_872_;
v_x_789_ = v___x_874_;
goto _start;
}
else
{
lean_object* v___f_876_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; uint8_t v___x_889_; 
lean_dec(v_x_789_);
v___f_876_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1));
v___x_889_ = l_Lean_Expr_isFVar(v_x_787_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
lean_dec(v_baseDeclName_x3f_785_);
lean_dec_ref(v_elimExpr_784_);
lean_dec_ref(v_a_783_);
v___x_890_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
v___x_891_ = l_Lean_indentExpr(v_type_786_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_892_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
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
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
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
lean_dec_ref(v_type_786_);
v___y_878_ = v___y_790_;
v___y_879_ = v___y_791_;
v___y_880_ = v___y_792_;
v___y_881_ = v___y_793_;
goto v___jp_877_;
}
v___jp_877_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_882_ = l_Array_takeWhile___redArg(v___f_876_, v_x_788_);
v___x_883_ = lean_array_get_size(v___x_882_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_array_get_size(v_x_788_);
v___x_886_ = lean_nat_dec_le(v___x_883_, v___x_884_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_883_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
v___y_796_ = v___y_881_;
v___y_797_ = v___y_880_;
v___y_798_ = v___x_882_;
v___y_799_ = v___y_879_;
v___y_800_ = v___y_878_;
v___y_801_ = v___x_887_;
goto v___jp_795_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_884_);
lean_ctor_set(v___x_888_, 1, v___x_885_);
v___y_796_ = v___y_881_;
v___y_797_ = v___y_880_;
v___y_798_ = v___x_882_;
v___y_799_ = v___y_879_;
v___y_800_ = v___y_878_;
v___y_801_ = v___x_888_;
goto v___jp_795_;
}
}
}
v___jp_795_:
{
lean_object* v___x_802_; 
lean_inc(v___y_796_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_800_);
lean_inc_ref(v_x_787_);
v___x_802_ = lean_infer_type(v_x_787_, v___y_800_, v___y_799_, v___y_797_, v___y_796_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___f_804_; uint8_t v___x_805_; lean_object* v___x_806_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_n(v_a_803_, 2);
lean_dec_ref_known(v___x_802_, 1);
lean_inc_ref(v_x_788_);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed), 9, 2);
lean_closure_set(v___f_804_, 0, v_a_803_);
lean_closure_set(v___f_804_, 1, v_x_788_);
v___x_805_ = 0;
v___x_806_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_803_, v___f_804_, v___x_805_, v___x_805_, v___y_800_, v___y_799_, v___y_797_, v___y_796_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_807_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_782_, v_x_787_);
if (lean_obj_tag(v___x_807_) == 1)
{
lean_object* v_val_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_val_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_807_, 1);
v_sz_809_ = lean_array_size(v___y_798_);
v___x_810_ = ((size_t)0ULL);
lean_inc_ref(v___y_798_);
lean_inc_ref(v_a_783_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_782_, v_a_783_, v_sz_809_, v___x_810_, v___y_798_, v___y_800_, v___y_799_, v___y_797_, v___y_796_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v_lower_814_; lean_object* v_upper_815_; lean_object* v_env_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = lean_st_ref_get(v___y_796_);
v_lower_814_ = lean_ctor_get(v___y_801_, 0);
lean_inc(v_lower_814_);
v_upper_815_ = lean_ctor_get(v___y_801_, 1);
lean_inc(v_upper_815_);
lean_dec_ref(v___y_801_);
v_env_816_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref(v_env_816_);
lean_dec(v___x_813_);
v___x_817_ = lean_array_get_size(v_xs_782_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0));
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_817_, v_xs_782_, v_x_787_, v___y_798_, v_baseDeclName_x3f_785_, v_env_816_, v___x_818_, v___x_819_, v___y_800_, v___y_797_, v___y_796_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_787_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_833_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_833_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v_start_826_; lean_object* v_stop_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_825_ = l_Array_toSubarray___redArg(v_x_788_, v_lower_814_, v_upper_815_);
v_start_826_ = lean_ctor_get(v___x_825_, 1);
lean_inc(v_start_826_);
v_stop_827_ = lean_ctor_get(v___x_825_, 2);
lean_inc(v_stop_827_);
lean_dec_ref(v___x_825_);
v___x_828_ = lean_nat_sub(v_stop_827_, v_start_826_);
lean_dec(v_start_826_);
lean_dec(v_stop_827_);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v_elimExpr_784_);
lean_ctor_set(v___x_829_, 1, v_a_783_);
lean_ctor_set(v___x_829_, 2, v_val_808_);
lean_ctor_set(v___x_829_, 3, v_a_812_);
lean_ctor_set(v___x_829_, 4, v_a_821_);
lean_ctor_set(v___x_829_, 5, v___x_828_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_829_);
v___x_831_ = v___x_823_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_upper_815_);
lean_dec(v_lower_814_);
lean_dec(v_a_812_);
lean_dec(v_val_808_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_elimExpr_784_);
lean_dec_ref(v_a_783_);
v_a_834_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_820_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_820_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_val_808_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
lean_dec(v_baseDeclName_x3f_785_);
lean_dec_ref(v_elimExpr_784_);
lean_dec_ref(v_a_783_);
v_a_842_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_811_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_811_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___x_807_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
lean_dec(v_baseDeclName_x3f_785_);
lean_dec_ref(v_elimExpr_784_);
v___x_850_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
v___x_851_ = l_Lean_indentExpr(v_a_783_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_852_, v___y_800_, v___y_799_, v___y_797_, v___y_796_);
return v___x_853_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v___y_801_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
lean_dec(v_baseDeclName_x3f_785_);
lean_dec_ref(v_elimExpr_784_);
lean_dec_ref(v_a_783_);
v_a_854_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_806_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_806_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___y_801_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
lean_dec(v_baseDeclName_x3f_785_);
lean_dec_ref(v_elimExpr_784_);
lean_dec_ref(v_a_783_);
v_a_862_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_802_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_802_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object* v_xs_902_, lean_object* v_a_903_, lean_object* v_elimExpr_904_, lean_object* v_baseDeclName_x3f_905_, lean_object* v_type_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_902_, v_a_903_, v_elimExpr_904_, v_baseDeclName_x3f_905_, v_type_906_, v_x_907_, v_x_908_, v_x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v_xs_902_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v_dummy_917_; 
v___x_916_ = lean_box(0);
v_dummy_917_ = l_Lean_Expr_sort___override(v___x_916_);
return v_dummy_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* v_a_918_, lean_object* v_elimExpr_919_, lean_object* v_baseDeclName_x3f_920_, lean_object* v_xs_921_, lean_object* v_type_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_dummy_928_; lean_object* v_nargs_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_dummy_928_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___lam__0___closed__0, &l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once, _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0);
v_nargs_929_ = l_Lean_Expr_getAppNumArgs(v_type_922_);
lean_inc(v_nargs_929_);
v___x_930_ = lean_mk_array(v_nargs_929_, v_dummy_928_);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_sub(v_nargs_929_, v___x_931_);
lean_dec(v_nargs_929_);
lean_inc_ref(v_type_922_);
v___x_933_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_921_, v_a_918_, v_elimExpr_919_, v_baseDeclName_x3f_920_, v_type_922_, v_type_922_, v___x_930_, v___x_932_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* v_a_934_, lean_object* v_elimExpr_935_, lean_object* v_baseDeclName_x3f_936_, lean_object* v_xs_937_, lean_object* v_type_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_getElimExprInfo___lam__0(v_a_934_, v_elimExpr_935_, v_baseDeclName_x3f_936_, v_xs_937_, v_type_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_xs_937_);
return v_res_944_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_945_; double v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_float_of_nat(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object* v_cls_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_ref_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1003_; 
v_ref_957_ = lean_ctor_get(v___y_954_, 5);
v___x_958_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1003_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1003_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v_traceState_964_; lean_object* v_env_965_; lean_object* v_nextMacroScope_966_; lean_object* v_ngen_967_; lean_object* v_auxDeclNGen_968_; lean_object* v_cache_969_; lean_object* v_messages_970_; lean_object* v_infoState_971_; lean_object* v_snapshotTasks_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1002_; 
v___x_963_ = lean_st_ref_take(v___y_955_);
v_traceState_964_ = lean_ctor_get(v___x_963_, 4);
v_env_965_ = lean_ctor_get(v___x_963_, 0);
v_nextMacroScope_966_ = lean_ctor_get(v___x_963_, 1);
v_ngen_967_ = lean_ctor_get(v___x_963_, 2);
v_auxDeclNGen_968_ = lean_ctor_get(v___x_963_, 3);
v_cache_969_ = lean_ctor_get(v___x_963_, 5);
v_messages_970_ = lean_ctor_get(v___x_963_, 6);
v_infoState_971_ = lean_ctor_get(v___x_963_, 7);
v_snapshotTasks_972_ = lean_ctor_get(v___x_963_, 8);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_974_ = v___x_963_;
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snapshotTasks_972_);
lean_inc(v_infoState_971_);
lean_inc(v_messages_970_);
lean_inc(v_cache_969_);
lean_inc(v_traceState_964_);
lean_inc(v_auxDeclNGen_968_);
lean_inc(v_ngen_967_);
lean_inc(v_nextMacroScope_966_);
lean_inc(v_env_965_);
lean_dec(v___x_963_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
uint64_t v_tid_976_; lean_object* v_traces_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1001_; 
v_tid_976_ = lean_ctor_get_uint64(v_traceState_964_, sizeof(void*)*1);
v_traces_977_ = lean_ctor_get(v_traceState_964_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_traceState_964_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_979_ = v_traceState_964_;
v_isShared_980_ = v_isSharedCheck_1001_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_traces_977_);
lean_dec(v_traceState_964_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1001_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; double v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_981_ = lean_box(0);
v___x_982_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0, &l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0);
v___x_983_ = 0;
v___x_984_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1));
v___x_985_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_985_, 0, v_cls_950_);
lean_ctor_set(v___x_985_, 1, v___x_981_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
lean_ctor_set_float(v___x_985_, sizeof(void*)*3, v___x_982_);
lean_ctor_set_float(v___x_985_, sizeof(void*)*3 + 8, v___x_982_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*3 + 16, v___x_983_);
v___x_986_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2));
v___x_987_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v_a_959_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
lean_inc(v_ref_957_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_ref_957_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_PersistentArray_push___redArg(v_traces_977_, v___x_988_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_989_);
v___x_991_ = v___x_979_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_989_);
lean_ctor_set_uint64(v_reuseFailAlloc_1000_, sizeof(void*)*1, v_tid_976_);
v___x_991_ = v_reuseFailAlloc_1000_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v___x_991_);
v___x_993_ = v___x_974_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_env_965_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_nextMacroScope_966_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_ngen_967_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_auxDeclNGen_968_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_cache_969_);
lean_ctor_set(v_reuseFailAlloc_999_, 6, v_messages_970_);
lean_ctor_set(v_reuseFailAlloc_999_, 7, v_infoState_971_);
lean_ctor_set(v_reuseFailAlloc_999_, 8, v_snapshotTasks_972_);
v___x_993_ = v_reuseFailAlloc_999_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_994_ = lean_st_ref_set(v___y_955_, v___x_993_);
v___x_995_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_995_);
v___x_997_ = v___x_961_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object* v_cls_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v_cls_1004_, v_msg_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__5(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1021_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__4));
v___x_1022_ = l_Lean_Name_append(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__7(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__6));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__9(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__8));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* v_elimExpr_1029_, lean_object* v_baseDeclName_x3f_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc(v_a_1034_);
lean_inc_ref(v_a_1033_);
lean_inc(v_a_1032_);
lean_inc_ref(v_a_1031_);
lean_inc_ref(v_elimExpr_1029_);
v___x_1036_ = lean_infer_type(v_elimExpr_1029_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_options_1037_; lean_object* v_a_1038_; lean_object* v_inheritedTraceOptions_1039_; uint8_t v_hasTrace_1040_; lean_object* v___f_1041_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; 
v_options_1037_ = lean_ctor_get(v_a_1033_, 2);
v_a_1038_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_n(v_a_1038_, 2);
lean_dec_ref_known(v___x_1036_, 1);
v_inheritedTraceOptions_1039_ = lean_ctor_get(v_a_1033_, 13);
v_hasTrace_1040_ = lean_ctor_get_uint8(v_options_1037_, sizeof(void*)*1);
lean_inc_ref(v_elimExpr_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1041_, 0, v_a_1038_);
lean_closure_set(v___f_1041_, 1, v_elimExpr_1029_);
lean_closure_set(v___f_1041_, 2, v_baseDeclName_x3f_1030_);
if (v_hasTrace_1040_ == 0)
{
lean_dec_ref(v_elimExpr_1029_);
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
v___y_1045_ = v_a_1033_;
v___y_1046_ = v_a_1034_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1050_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__5, &l_Lean_Meta_getElimExprInfo___closed__5_once, _init_l_Lean_Meta_getElimExprInfo___closed__5);
v___x_1051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1039_, v_options_1037_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_elimExpr_1029_);
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
v___y_1045_ = v_a_1033_;
v___y_1046_ = v_a_1034_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1052_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__7, &l_Lean_Meta_getElimExprInfo___closed__7_once, _init_l_Lean_Meta_getElimExprInfo___closed__7);
v___x_1053_ = l_Lean_indentExpr(v_elimExpr_1029_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__9, &l_Lean_Meta_getElimExprInfo___closed__9_once, _init_l_Lean_Meta_getElimExprInfo___closed__9);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc(v_a_1038_);
v___x_1057_ = l_Lean_indentExpr(v_a_1038_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v___x_1049_, v___x_1058_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_dec_ref_known(v___x_1059_, 1);
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
v___y_1045_ = v_a_1033_;
v___y_1046_ = v_a_1034_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v___f_1041_);
lean_dec(v_a_1038_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
v___jp_1042_:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = 0;
v___x_1048_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_1038_, v___f_1041_, v___x_1047_, v___x_1047_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1048_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_baseDeclName_x3f_1030_);
lean_dec_ref(v_elimExpr_1029_);
v_a_1068_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1036_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1036_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object* v_elimExpr_1076_, lean_object* v_baseDeclName_x3f_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_getElimExprInfo(v_elimExpr_1076_, v_baseDeclName_x3f_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object* v_00_u03b1_1084_, lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(v_00_u03b1_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object* v_upperBound_1100_, lean_object* v_xs_1101_, lean_object* v_motive_1102_, lean_object* v___x_1103_, lean_object* v_baseDeclName_x3f_1104_, lean_object* v___x_1105_, lean_object* v_inst_1106_, lean_object* v_R_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v_c_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_1100_, v_xs_1101_, v_motive_1102_, v___x_1103_, v_baseDeclName_x3f_1104_, v___x_1105_, v_a_1108_, v_b_1109_, v___y_1111_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* v_upperBound_1117_, lean_object* v_xs_1118_, lean_object* v_motive_1119_, lean_object* v___x_1120_, lean_object* v_baseDeclName_x3f_1121_, lean_object* v___x_1122_, lean_object* v_inst_1123_, lean_object* v_R_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(v_upperBound_1117_, v_xs_1118_, v_motive_1119_, v___x_1120_, v_baseDeclName_x3f_1121_, v___x_1122_, v_inst_1123_, v_R_1124_, v_a_1125_, v_b_1126_, v_c_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v___x_1120_);
lean_dec_ref(v_motive_1119_);
lean_dec_ref(v_xs_1118_);
lean_dec(v_upperBound_1117_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* v_elimName_1134_, lean_object* v_baseDeclName_x3f_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_elimName_1134_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_Meta_getElimExprInfo(v_a_1142_, v_baseDeclName_x3f_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_baseDeclName_x3f_1135_);
v_a_1144_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1141_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object* v_elimName_1152_, lean_object* v_baseDeclName_x3f_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_getElimInfo(v_elimName_1152_, v_baseDeclName_x3f_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* v_a_1160_, lean_object* v_as_1161_, size_t v_i_1162_, size_t v_stop_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_eq(v_i_1162_, v_stop_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_array_uget_borrowed(v_as_1161_, v_i_1162_);
v___x_1166_ = lean_nat_dec_eq(v_a_1160_, v___x_1165_);
if (v___x_1166_ == 0)
{
size_t v___x_1167_; size_t v___x_1168_; 
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1162_, v___x_1167_);
v_i_1162_ = v___x_1168_;
goto _start;
}
else
{
return v___x_1166_;
}
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* v_a_1171_, lean_object* v_as_1172_, lean_object* v_i_1173_, lean_object* v_stop_1174_){
_start:
{
size_t v_i_boxed_1175_; size_t v_stop_boxed_1176_; uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_i_boxed_1175_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_stop_boxed_1176_ = lean_unbox_usize(v_stop_1174_);
lean_dec(v_stop_1174_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1171_, v_as_1172_, v_i_boxed_1175_, v_stop_boxed_1176_);
lean_dec_ref(v_as_1172_);
lean_dec(v_a_1171_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* v_as_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_array_get_size(v_as_1179_);
v___x_1183_ = lean_nat_dec_lt(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
return v___x_1183_;
}
else
{
if (v___x_1183_ == 0)
{
return v___x_1183_;
}
else
{
size_t v___x_1184_; size_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = lean_usize_of_nat(v___x_1182_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1180_, v_as_1179_, v___x_1184_, v___x_1185_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* v_as_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_as_1187_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7));
v___x_1204_ = l_Lean_stringToMessageData(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object* v_elimInfo_1208_, lean_object* v_targets_1209_, lean_object* v_type_1210_, lean_object* v_argIdx_1211_, lean_object* v_targetIdx_1212_, lean_object* v_implicits_1213_, lean_object* v_targets_x27_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Meta_whnfD(v_type_1210_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
if (lean_obj_tag(v_a_1224_) == 7)
{
lean_object* v_binderName_1225_; lean_object* v_binderType_1226_; lean_object* v_body_1227_; uint8_t v_binderInfo_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v_elimExpr_1296_; lean_object* v_targetsPos_1297_; uint8_t v___x_1298_; 
v_binderName_1225_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_binderName_1225_);
v_binderType_1226_ = lean_ctor_get(v_a_1224_, 1);
lean_inc_ref(v_binderType_1226_);
v_body_1227_ = lean_ctor_get(v_a_1224_, 2);
lean_inc_ref(v_body_1227_);
v_binderInfo_1228_ = lean_ctor_get_uint8(v_a_1224_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1224_, 3);
v_elimExpr_1296_ = lean_ctor_get(v_elimInfo_1208_, 0);
v_targetsPos_1297_ = lean_ctor_get(v_elimInfo_1208_, 3);
v___x_1298_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_1297_, v_argIdx_1211_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_binderName_1225_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_binderType_1226_);
v___x_1300_ = 0;
v___x_1301_ = lean_box(0);
v___x_1302_ = l_Lean_Meta_mkFreshExprMVar(v___x_1299_, v___x_1300_, v___x_1301_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = lean_expr_instantiate1(v_body_1227_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_body_1227_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_nat_add(v_argIdx_1211_, v___x_1305_);
lean_dec(v_argIdx_1211_);
v_type_1210_ = v___x_1304_;
v_argIdx_1211_ = v___x_1306_;
goto _start;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1308_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1302_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1302_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1228_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_binderType_1226_);
v___x_1318_ = 0;
v___x_1319_ = l_Lean_Meta_mkFreshExprMVar(v___x_1317_, v___x_1318_, v_binderName_1225_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = lean_expr_instantiate1(v_body_1227_, v_a_1320_);
lean_dec_ref(v_body_1227_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_nat_add(v_argIdx_1211_, v___x_1322_);
lean_dec(v_argIdx_1211_);
v___x_1324_ = l_Lean_Expr_mvarId_x21(v_a_1320_);
v___x_1325_ = lean_array_push(v_implicits_1213_, v___x_1324_);
v___x_1326_ = lean_array_push(v_targets_x27_1214_, v_a_1320_);
v_type_1210_ = v___x_1321_;
v_argIdx_1211_ = v___x_1323_;
v_implicits_1213_ = v___x_1325_;
v_targets_x27_1214_ = v___x_1326_;
goto _start;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1328_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1319_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1319_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
lean_dec(v_binderName_1225_);
v___x_1336_ = lean_array_get_size(v_targets_1209_);
v___x_1337_ = lean_nat_dec_lt(v_targetIdx_1212_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
lean_inc_ref(v_elimExpr_1296_);
v___x_1339_ = l_Lean_MessageData_ofExpr(v_elimExpr_1296_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1342_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref_known(v___x_1343_, 1);
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
v___y_1244_ = v_a_1217_;
v___y_1245_ = v_a_1218_;
goto v___jp_1241_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
v___y_1244_ = v_a_1217_;
v___y_1245_ = v_a_1218_;
goto v___jp_1241_;
}
}
}
v___jp_1229_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1235_ = lean_expr_instantiate1(v_body_1227_, v___y_1230_);
lean_dec_ref(v_body_1227_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_argIdx_1211_, v___x_1236_);
lean_dec(v_argIdx_1211_);
v___x_1238_ = lean_nat_add(v_targetIdx_1212_, v___x_1236_);
lean_dec(v_targetIdx_1212_);
v___x_1239_ = lean_array_push(v_targets_x27_1214_, v___y_1230_);
v_type_1210_ = v___x_1235_;
v_argIdx_1211_ = v___x_1237_;
v_targetIdx_1212_ = v___x_1238_;
v_targets_x27_1214_ = v___x_1239_;
v_a_1215_ = v___y_1231_;
v_a_1216_ = v___y_1232_;
v_a_1217_ = v___y_1233_;
v_a_1218_ = v___y_1234_;
goto _start;
}
v___jp_1241_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_instInhabitedExpr;
v___x_1247_ = lean_array_get_borrowed(v___x_1246_, v_targets_1209_, v_targetIdx_1212_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___x_1247_);
v___x_1248_ = lean_infer_type(v___x_1247_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_n(v_a_1249_, 2);
lean_dec_ref_known(v___x_1248_, 1);
lean_inc_ref(v_binderType_1226_);
v___x_1250_ = l_Lean_Meta_isExprDefEq(v_binderType_1226_, v_a_1249_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; uint8_t v___x_1252_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = lean_unbox(v_a_1251_);
lean_dec(v_a_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0));
v___x_1255_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_1249_, v_binderType_1226_, v___x_1253_, v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
lean_inc(v___x_1247_);
v___x_1258_ = l_Lean_indentExpr(v___x_1247_);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_1256_);
v___x_1263_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1262_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_dec_ref_known(v___x_1263_, 1);
lean_inc(v___x_1247_);
v___y_1230_ = v___x_1247_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
v___y_1233_ = v___y_1244_;
v___y_1234_ = v___y_1245_;
goto v___jp_1229_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1272_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1255_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1255_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_dec(v_a_1249_);
lean_dec_ref(v_binderType_1226_);
lean_inc(v___x_1247_);
v___y_1230_ = v___x_1247_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
v___y_1233_ = v___y_1244_;
v___y_1234_ = v___y_1245_;
goto v___jp_1229_;
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_a_1249_);
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1280_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1250_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1250_);
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
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_body_1227_);
lean_dec_ref(v_binderType_1226_);
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1288_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1248_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1248_);
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
lean_object* v___x_1352_; uint8_t v___x_1353_; 
lean_dec(v_a_1224_);
lean_dec(v_argIdx_1211_);
v___x_1352_ = lean_array_get_size(v_targets_1209_);
v___x_1353_ = lean_nat_dec_eq(v_targetIdx_1212_, v___x_1352_);
lean_dec(v_targetIdx_1212_);
if (v___x_1353_ == 0)
{
lean_object* v_elimExpr_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_elimExpr_1354_ = lean_ctor_get(v_elimInfo_1208_, 0);
lean_inc_ref(v_elimExpr_1354_);
lean_dec_ref(v_elimInfo_1208_);
v___x_1355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
v___x_1356_ = l_Lean_MessageData_ofExpr(v_elimExpr_1354_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1359_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
goto v___jp_1220_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_dec_ref(v_elimInfo_1208_);
goto v___jp_1220_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_targets_x27_1214_);
lean_dec_ref(v_implicits_1213_);
lean_dec(v_targetIdx_1212_);
lean_dec(v_argIdx_1211_);
lean_dec_ref(v_elimInfo_1208_);
v_a_1369_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1223_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1223_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_implicits_1213_);
lean_ctor_set(v___x_1221_, 1, v_targets_x27_1214_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object* v_elimInfo_1377_, lean_object* v_targets_1378_, lean_object* v_type_1379_, lean_object* v_argIdx_1380_, lean_object* v_targetIdx_1381_, lean_object* v_implicits_1382_, lean_object* v_targets_x27_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1377_, v_targets_1378_, v_type_1379_, v_argIdx_1380_, v_targetIdx_1381_, v_implicits_1382_, v_targets_x27_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec_ref(v_targets_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object* v_e_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = l_Lean_Expr_hasMVar(v_e_1390_);
v___x_1394_ = lean_bool_not(v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v_mctx_1396_; lean_object* v___x_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1400_; lean_object* v_cache_1401_; lean_object* v_zetaDeltaFVarIds_1402_; lean_object* v_postponed_1403_; lean_object* v_diag_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v___x_1395_ = lean_st_ref_get(v___y_1391_);
v_mctx_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc_ref(v_mctx_1396_);
lean_dec(v___x_1395_);
v___x_1397_ = l_Lean_instantiateMVarsCore(v_mctx_1396_, v_e_1390_);
v_fst_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_fst_1398_);
v_snd_1399_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_snd_1399_);
lean_dec_ref(v___x_1397_);
v___x_1400_ = lean_st_ref_take(v___y_1391_);
v_cache_1401_ = lean_ctor_get(v___x_1400_, 1);
v_zetaDeltaFVarIds_1402_ = lean_ctor_get(v___x_1400_, 2);
v_postponed_1403_ = lean_ctor_get(v___x_1400_, 3);
v_diag_1404_ = lean_ctor_get(v___x_1400_, 4);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1414_);
v___x_1406_ = v___x_1400_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_diag_1404_);
lean_inc(v_postponed_1403_);
lean_inc(v_zetaDeltaFVarIds_1402_);
lean_inc(v_cache_1401_);
lean_dec(v___x_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_snd_1399_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_snd_1399_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_cache_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_zetaDeltaFVarIds_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_postponed_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_diag_1404_);
v___x_1409_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_st_ref_set(v___y_1391_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_fst_1398_);
return v___x_1411_;
}
}
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_e_1390_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object* v_e_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1416_, v___y_1417_);
lean_dec(v___y_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object* v_e_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1420_, v___y_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object* v_e_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(v_e_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1434_, lean_object* v_i_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_array_get_size(v_keys_1434_);
v___x_1438_ = lean_nat_dec_lt(v_i_1435_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_dec(v_i_1435_);
return v___x_1438_;
}
else
{
lean_object* v_k_x27_1439_; uint8_t v___x_1440_; 
v_k_x27_1439_ = lean_array_fget_borrowed(v_keys_1434_, v_i_1435_);
v___x_1440_ = l_Lean_instBEqMVarId_beq(v_k_1436_, v_k_x27_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_add(v_i_1435_, v___x_1441_);
lean_dec(v_i_1435_);
v_i_1435_ = v___x_1442_;
goto _start;
}
else
{
lean_dec(v_i_1435_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1444_, lean_object* v_i_1445_, lean_object* v_k_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1444_, v_i_1445_, v_k_1446_);
lean_dec(v_k_1446_);
lean_dec_ref(v_keys_1444_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1449_, size_t v_x_1450_, lean_object* v_x_1451_){
_start:
{
if (lean_obj_tag(v_x_1449_) == 0)
{
lean_object* v_es_1452_; lean_object* v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v_j_1456_; lean_object* v___x_1457_; 
v_es_1452_ = lean_ctor_get(v_x_1449_, 0);
v___x_1453_ = lean_box(2);
v___x_1454_ = ((size_t)31ULL);
v___x_1455_ = lean_usize_land(v_x_1450_, v___x_1454_);
v_j_1456_ = lean_usize_to_nat(v___x_1455_);
v___x_1457_ = lean_array_get_borrowed(v___x_1453_, v_es_1452_, v_j_1456_);
lean_dec(v_j_1456_);
switch(lean_obj_tag(v___x_1457_))
{
case 0:
{
lean_object* v_key_1458_; uint8_t v___x_1459_; 
v_key_1458_ = lean_ctor_get(v___x_1457_, 0);
v___x_1459_ = l_Lean_instBEqMVarId_beq(v_x_1451_, v_key_1458_);
return v___x_1459_;
}
case 1:
{
lean_object* v_node_1460_; size_t v___x_1461_; size_t v___x_1462_; 
v_node_1460_ = lean_ctor_get(v___x_1457_, 0);
v___x_1461_ = ((size_t)5ULL);
v___x_1462_ = lean_usize_shift_right(v_x_1450_, v___x_1461_);
v_x_1449_ = v_node_1460_;
v_x_1450_ = v___x_1462_;
goto _start;
}
default: 
{
uint8_t v___x_1464_; 
v___x_1464_ = 0;
return v___x_1464_;
}
}
}
else
{
lean_object* v_ks_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_ks_1465_ = lean_ctor_get(v_x_1449_, 0);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1465_, v___x_1466_, v_x_1451_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
size_t v_x_3339__boxed_1471_; uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_x_3339__boxed_1471_ = lean_unbox_usize(v_x_1469_);
lean_dec(v_x_1469_);
v_res_1472_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1468_, v_x_3339__boxed_1471_, v_x_1470_);
lean_dec(v_x_1470_);
lean_dec_ref(v_x_1468_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
uint64_t v___x_1476_; size_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = l_Lean_instHashableMVarId_hash(v_x_1475_);
v___x_1477_ = lean_uint64_to_usize(v___x_1476_);
v___x_1478_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1474_, v___x_1477_, v_x_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1479_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec_ref(v_x_1479_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* v_mvarId_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v_mctx_1487_; lean_object* v_eAssignment_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = lean_st_ref_get(v___y_1484_);
v_mctx_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_mctx_1487_);
lean_dec(v___x_1486_);
v_eAssignment_1488_ = lean_ctor_get(v_mctx_1487_, 8);
lean_inc_ref(v_eAssignment_1488_);
lean_dec_ref(v_mctx_1487_);
v___x_1489_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_1488_, v_mvarId_1483_);
lean_dec_ref(v_eAssignment_1488_);
v___x_1490_ = lean_box(v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* v_mvarId_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec(v_mvarId_1492_);
return v_res_1495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object* v_as_1502_, size_t v_sz_1503_, size_t v_i_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_a_1512_; uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1504_, v_sz_1503_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_b_1505_);
return v___x_1517_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_array_uget_borrowed(v_as_1502_, v_i_1504_);
v___x_1519_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_1518_, v___y_1507_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_unbox(v_a_1520_);
lean_dec(v_a_1520_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_inc(v_a_1518_);
v___x_1523_ = l_Lean_MVarId_getDecl(v_a_1518_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_userName_1528_; uint8_t v___x_1529_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v_userName_1528_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_userName_1528_);
lean_dec(v_a_1524_);
v___x_1529_ = l_Lean_Name_isAnonymous(v_userName_1528_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_Name_hasMacroScopes(v_userName_1528_);
lean_dec(v_userName_1528_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_a_1518_);
v___x_1531_ = l_Lean_MVarId_getDecl(v_a_1518_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_userName_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_userName_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_userName_1533_);
lean_dec(v_a_1532_);
v___x_1534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
v___x_1535_ = l_Lean_MessageData_ofName(v_userName_1533_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1538_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_dec_ref_known(v___x_1539_, 1);
v_a_1512_ = v___x_1521_;
goto v___jp_1511_;
}
else
{
return v___x_1539_;
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1531_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1531_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
goto v___jp_1525_;
}
}
else
{
lean_dec(v_userName_1528_);
goto v___jp_1525_;
}
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
v___x_1527_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1526_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_dec_ref_known(v___x_1527_, 1);
v_a_1512_ = v___x_1521_;
goto v___jp_1511_;
}
else
{
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1523_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1523_);
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
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
v_a_1512_ = v___x_1521_;
goto v___jp_1511_;
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1519_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1519_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
v___jp_1511_:
{
size_t v___x_1513_; size_t v___x_1514_; 
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1504_, v___x_1513_);
v_i_1504_ = v___x_1514_;
v_b_1505_ = v_a_1512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
size_t v_sz_boxed_1573_; size_t v_i_boxed_1574_; lean_object* v_res_1575_; 
v_sz_boxed_1573_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1574_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_1564_, v_sz_boxed_1573_, v_i_boxed_1574_, v_b_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_as_1564_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t v_sz_1576_, size_t v_i_1577_, lean_object* v_bs_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_usize_dec_lt(v_i_1577_, v_sz_1576_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_bs_1578_);
return v___x_1585_;
}
else
{
lean_object* v_v_1586_; lean_object* v___x_1587_; 
v_v_1586_ = lean_array_uget_borrowed(v_bs_1578_, v_i_1577_);
lean_inc(v_v_1586_);
v___x_1587_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_1586_, v___y_1580_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v_bs_x27_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = lean_unsigned_to_nat(0u);
v_bs_x27_1590_ = lean_array_uset(v_bs_1578_, v_i_1577_, v___x_1589_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1577_, v___x_1591_);
v___x_1593_ = lean_array_uset(v_bs_x27_1590_, v_i_1577_, v_a_1588_);
v_i_1577_ = v___x_1592_;
v_bs_1578_ = v___x_1593_;
goto _start;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_bs_1578_);
v_a_1595_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1587_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1587_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_bs_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_1611_, v_i_boxed_1612_, v_bs_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* v_elimInfo_1616_, lean_object* v_targets_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_elimType_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_elimType_1623_ = lean_ctor_get(v_elimInfo_1616_, 1);
lean_inc_ref(v_elimType_1623_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_1626_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1616_, v_targets_1617_, v_elimType_1623_, v___x_1624_, v___x_1624_, v___x_1625_, v___x_1625_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v___x_1630_; size_t v_sz_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_fst_1628_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v_a_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec(v_a_1627_);
v___x_1630_ = lean_box(0);
v_sz_1631_ = lean_array_size(v_fst_1628_);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_1628_, v_sz_1631_, v___x_1632_, v___x_1630_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_fst_1628_);
if (lean_obj_tag(v___x_1633_) == 0)
{
size_t v_sz_1634_; lean_object* v___x_1635_; 
lean_dec_ref_known(v___x_1633_, 1);
v_sz_1634_ = lean_array_size(v_snd_1629_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_1634_, v___x_1632_, v_snd_1629_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
return v___x_1635_;
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_snd_1629_);
v_a_1636_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1633_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1633_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1626_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1626_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* v_elimInfo_1652_, lean_object* v_targets_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_addImplicitTargets(v_elimInfo_1652_, v_targets_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec_ref(v_targets_1653_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object* v_mvarId_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1660_, v___y_1662_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* v_mvarId_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(v_mvarId_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v_mvarId_1667_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* v_00_u03b2_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1675_, v_x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_1678_, v_x_1679_, v_x_1680_);
lean_dec(v_x_1680_);
lean_dec_ref(v_x_1679_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1683_, lean_object* v_x_1684_, size_t v_x_1685_, lean_object* v_x_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1684_, v_x_1685_, v_x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
size_t v_x_3682__boxed_1692_; uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_x_3682__boxed_1692_ = lean_unbox_usize(v_x_1690_);
lean_dec(v_x_1690_);
v_res_1693_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_1688_, v_x_1689_, v_x_3682__boxed_1692_, v_x_1691_);
lean_dec(v_x_1691_);
lean_dec_ref(v_x_1689_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1695_, lean_object* v_keys_1696_, lean_object* v_vals_1697_, lean_object* v_heq_1698_, lean_object* v_i_1699_, lean_object* v_k_1700_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1696_, v_i_1699_, v_k_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1702_, lean_object* v_keys_1703_, lean_object* v_vals_1704_, lean_object* v_heq_1705_, lean_object* v_i_1706_, lean_object* v_k_1707_){
_start:
{
uint8_t v_res_1708_; lean_object* v_r_1709_; 
v_res_1708_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1702_, v_keys_1703_, v_vals_1704_, v_heq_1705_, v_i_1706_, v_k_1707_);
lean_dec(v_k_1707_);
lean_dec_ref(v_vals_1704_);
lean_dec_ref(v_keys_1703_);
v_r_1709_ = lean_box(v_res_1708_);
return v_r_1709_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 0)
{
lean_dec(v_x_1718_);
return v_x_1719_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
v_head_1721_ = lean_ctor_get(v_x_1720_, 0);
v_tail_1722_ = lean_ctor_get(v_x_1720_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1720_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1724_ = v_x_1720_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
lean_dec(v_x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
lean_inc(v_x_1718_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 5);
lean_ctor_set(v___x_1724_, 1, v_x_1718_);
lean_ctor_set(v___x_1724_, 0, v_x_1719_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_x_1718_);
v___x_1727_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = l_Lean_Name_reprPrec(v_head_1721_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1727_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v_x_1719_ = v___x_1730_;
v_x_1720_ = v_tail_1722_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_dec(v_x_1734_);
return v_x_1735_;
}
else
{
lean_object* v_head_1737_; lean_object* v_tail_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1749_; 
v_head_1737_ = lean_ctor_get(v_x_1736_, 0);
v_tail_1738_ = lean_ctor_get(v_x_1736_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1740_ = v_x_1736_;
v_isShared_1741_ = v_isSharedCheck_1749_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_tail_1738_);
lean_inc(v_head_1737_);
lean_dec(v_x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1749_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
lean_inc(v_x_1734_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 5);
lean_ctor_set(v___x_1740_, 1, v_x_1734_);
lean_ctor_set(v___x_1740_, 0, v_x_1735_);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_x_1735_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_x_1734_);
v___x_1743_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = l_Lean_Name_reprPrec(v_head_1737_, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1743_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_1734_, v___x_1746_, v_tail_1738_);
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = l_Lean_Name_reprPrec(v___y_1750_, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v___x_1755_; 
lean_dec(v_x_1754_);
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
else
{
lean_object* v_tail_1756_; 
v_tail_1756_ = lean_ctor_get(v_x_1753_, 1);
if (lean_obj_tag(v_tail_1756_) == 0)
{
lean_object* v_head_1757_; lean_object* v___x_1758_; 
lean_dec(v_x_1754_);
v_head_1757_ = lean_ctor_get(v_x_1753_, 0);
lean_inc(v_head_1757_);
lean_dec_ref_known(v_x_1753_, 2);
v___x_1758_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1757_);
return v___x_1758_;
}
else
{
lean_object* v_head_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_inc(v_tail_1756_);
v_head_1759_ = lean_ctor_get(v_x_1753_, 0);
lean_inc(v_head_1759_);
lean_dec_ref_known(v_x_1753_, 2);
v___x_1760_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1759_);
v___x_1761_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_1754_, v___x_1760_, v_tail_1756_);
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object* v_xs_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = lean_array_get_size(v_xs_1762_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_nat_dec_eq(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1766_ = lean_array_to_list(v_xs_1762_);
v___x_1767_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_1768_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_1766_, v___x_1767_);
v___x_1769_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_1770_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_1771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1768_);
v___x_1772_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_1773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1769_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Std_Format_fill(v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; 
lean_dec_ref(v_xs_1762_);
v___x_1776_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object* v_x_1791_){
_start:
{
uint8_t v_induction_1792_; lean_object* v_typeNames_1793_; lean_object* v_elimName_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_induction_1792_ = lean_ctor_get_uint8(v_x_1791_, sizeof(void*)*2);
v_typeNames_1793_ = lean_ctor_get(v_x_1791_, 0);
lean_inc_ref(v_typeNames_1793_);
v_elimName_1794_ = lean_ctor_get(v_x_1791_, 1);
lean_inc(v_elimName_1794_);
lean_dec_ref(v_x_1791_);
v___x_1795_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_1796_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2));
v___x_1797_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = l_Bool_repr___redArg(v_induction_1792_);
v___x_1800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1797_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = 0;
v___x_1802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1796_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_1805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_box(1);
v___x_1807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4));
v___x_1809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___x_1795_);
v___x_1811_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_1793_);
v___x_1812_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1797_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set_uint8(v___x_1813_, sizeof(void*)*1, v___x_1801_);
v___x_1814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1810_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1804_);
v___x_1816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1806_);
v___x_1817_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6));
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1795_);
v___x_1820_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_1821_ = l_Lean_Name_reprPrec(v_elimName_1794_, v___x_1798_);
v___x_1822_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*1, v___x_1801_);
v___x_1824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1819_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_1826_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_1827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1824_);
v___x_1828_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_1829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1825_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*1, v___x_1801_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object* v_x_1832_, lean_object* v_prec_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object* v_x_1835_, lean_object* v_prec_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_1835_, v_prec_1836_);
lean_dec(v_prec_1836_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_unsigned_to_nat(16u);
v___x_1842_ = lean_mk_array(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2(void){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3);
v___x_1850_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1);
v___x_1851_ = 1;
v___x_1852_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1849_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*2, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default(void){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators(void){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_f_1855_, lean_object* v_x1_1856_, lean_object* v_x2_1857_, lean_object* v_x3_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_apply_3(v_f_1855_, v_x1_1856_, v_x2_1857_, v_x3_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object* v_f_1860_, lean_object* v_keys_1861_, lean_object* v_vals_1862_, lean_object* v_i_1863_, lean_object* v_acc_1864_){
_start:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = lean_array_get_size(v_keys_1861_);
v___x_1866_ = lean_nat_dec_lt(v_i_1863_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec(v_i_1863_);
lean_dec(v_f_1860_);
return v_acc_1864_;
}
else
{
lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_k_1867_ = lean_array_fget_borrowed(v_keys_1861_, v_i_1863_);
v_v_1868_ = lean_array_fget_borrowed(v_vals_1862_, v_i_1863_);
lean_inc(v_f_1860_);
lean_inc(v_v_1868_);
lean_inc(v_k_1867_);
v___x_1869_ = lean_apply_3(v_f_1860_, v_acc_1864_, v_k_1867_, v_v_1868_);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_add(v_i_1863_, v___x_1870_);
lean_dec(v_i_1863_);
v_i_1863_ = v___x_1871_;
v_acc_1864_ = v___x_1869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object* v_f_1873_, lean_object* v_keys_1874_, lean_object* v_vals_1875_, lean_object* v_i_1876_, lean_object* v_acc_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1873_, v_keys_1874_, v_vals_1875_, v_i_1876_, v_acc_1877_);
lean_dec_ref(v_vals_1875_);
lean_dec_ref(v_keys_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v_es_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_es_1882_ = lean_ctor_get(v_x_1880_, 0);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_get_size(v_es_1882_);
v___x_1885_ = lean_nat_dec_lt(v___x_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v_f_1879_);
return v_x_1881_;
}
else
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_le(v___x_1884_, v___x_1884_);
if (v___x_1886_ == 0)
{
if (v___x_1885_ == 0)
{
lean_dec(v_f_1879_);
return v_x_1881_;
}
else
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_of_nat(v___x_1884_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1879_, v_es_1882_, v___x_1887_, v___x_1888_, v_x_1881_);
return v___x_1889_;
}
}
else
{
size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = lean_usize_of_nat(v___x_1884_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1879_, v_es_1882_, v___x_1890_, v___x_1891_, v_x_1881_);
return v___x_1892_;
}
}
}
else
{
lean_object* v_ks_1893_; lean_object* v_vs_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_ks_1893_ = lean_ctor_get(v_x_1880_, 0);
v_vs_1894_ = lean_ctor_get(v_x_1880_, 1);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1879_, v_ks_1893_, v_vs_1894_, v___x_1895_, v_x_1881_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object* v_f_1897_, lean_object* v_as_1898_, size_t v_i_1899_, size_t v_stop_1900_, lean_object* v_b_1901_){
_start:
{
lean_object* v___y_1903_; uint8_t v___x_1907_; 
v___x_1907_ = lean_usize_dec_eq(v_i_1899_, v_stop_1900_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_array_uget_borrowed(v_as_1898_, v_i_1899_);
switch(lean_obj_tag(v___x_1908_))
{
case 0:
{
lean_object* v_key_1909_; lean_object* v_val_1910_; lean_object* v___x_1911_; 
v_key_1909_ = lean_ctor_get(v___x_1908_, 0);
v_val_1910_ = lean_ctor_get(v___x_1908_, 1);
lean_inc(v_f_1897_);
lean_inc(v_val_1910_);
lean_inc(v_key_1909_);
v___x_1911_ = lean_apply_3(v_f_1897_, v_b_1901_, v_key_1909_, v_val_1910_);
v___y_1903_ = v___x_1911_;
goto v___jp_1902_;
}
case 1:
{
lean_object* v_node_1912_; lean_object* v___x_1913_; 
v_node_1912_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_f_1897_);
v___x_1913_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1897_, v_node_1912_, v_b_1901_);
v___y_1903_ = v___x_1913_;
goto v___jp_1902_;
}
default: 
{
v___y_1903_ = v_b_1901_;
goto v___jp_1902_;
}
}
}
else
{
lean_dec(v_f_1897_);
return v_b_1901_;
}
v___jp_1902_:
{
size_t v___x_1904_; size_t v___x_1905_; 
v___x_1904_ = ((size_t)1ULL);
v___x_1905_ = lean_usize_add(v_i_1899_, v___x_1904_);
v_i_1899_ = v___x_1905_;
v_b_1901_ = v___y_1903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_f_1914_, lean_object* v_as_1915_, lean_object* v_i_1916_, lean_object* v_stop_1917_, lean_object* v_b_1918_){
_start:
{
size_t v_i_boxed_1919_; size_t v_stop_boxed_1920_; lean_object* v_res_1921_; 
v_i_boxed_1919_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_stop_boxed_1920_ = lean_unbox_usize(v_stop_1917_);
lean_dec(v_stop_1917_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1914_, v_as_1915_, v_i_boxed_1919_, v_stop_boxed_1920_, v_b_1918_);
lean_dec_ref(v_as_1915_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1922_, v_x_1923_, v_x_1924_);
lean_dec_ref(v_x_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_1926_, lean_object* v_f_1927_, lean_object* v_init_1928_){
_start:
{
lean_object* v___f_1929_; lean_object* v___x_1930_; 
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1929_, 0, v_f_1927_);
v___x_1930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_1929_, v_map_1926_, v_init_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_1931_, lean_object* v_f_1932_, lean_object* v_init_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_1931_, v_f_1932_, v_init_1933_);
lean_dec_ref(v_map_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
lean_dec(v_f_1935_);
return v_x_1936_;
}
else
{
lean_object* v_key_1938_; lean_object* v_value_1939_; lean_object* v_tail_1940_; lean_object* v___x_1941_; 
v_key_1938_ = lean_ctor_get(v_x_1937_, 0);
lean_inc(v_key_1938_);
v_value_1939_ = lean_ctor_get(v_x_1937_, 1);
lean_inc(v_value_1939_);
v_tail_1940_ = lean_ctor_get(v_x_1937_, 2);
lean_inc(v_tail_1940_);
lean_dec_ref_known(v_x_1937_, 3);
lean_inc(v_f_1935_);
v___x_1941_ = lean_apply_3(v_f_1935_, v_x_1936_, v_key_1938_, v_value_1939_);
v_x_1936_ = v___x_1941_;
v_x_1937_ = v_tail_1940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object* v_f_1943_, lean_object* v_as_1944_, size_t v_i_1945_, size_t v_stop_1946_, lean_object* v_b_1947_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_usize_dec_eq(v_i_1945_, v_stop_1946_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; 
v___x_1949_ = lean_array_uget_borrowed(v_as_1944_, v_i_1945_);
lean_inc(v___x_1949_);
lean_inc(v_f_1943_);
v___x_1950_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1943_, v_b_1947_, v___x_1949_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1945_, v___x_1951_);
v_i_1945_ = v___x_1952_;
v_b_1947_ = v___x_1950_;
goto _start;
}
else
{
lean_dec(v_f_1943_);
return v_b_1947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_f_1954_, lean_object* v_as_1955_, lean_object* v_i_1956_, lean_object* v_stop_1957_, lean_object* v_b_1958_){
_start:
{
size_t v_i_boxed_1959_; size_t v_stop_boxed_1960_; lean_object* v_res_1961_; 
v_i_boxed_1959_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_stop_boxed_1960_ = lean_unbox_usize(v_stop_1957_);
lean_dec(v_stop_1957_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1954_, v_as_1955_, v_i_boxed_1959_, v_stop_boxed_1960_, v_b_1958_);
lean_dec_ref(v_as_1955_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object* v_f_1962_, lean_object* v_init_1963_, lean_object* v_m_1964_){
_start:
{
lean_object* v_map_u2081_1965_; lean_object* v_map_u2082_1966_; lean_object* v_buckets_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_map_u2081_1965_ = lean_ctor_get(v_m_1964_, 0);
v_map_u2082_1966_ = lean_ctor_get(v_m_1964_, 1);
v_buckets_1967_ = lean_ctor_get(v_map_u2081_1965_, 1);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_array_get_size(v_buckets_1967_);
v___x_1970_ = lean_nat_dec_lt(v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1966_, v_f_1962_, v_init_1963_);
return v___x_1971_;
}
else
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_nat_dec_le(v___x_1969_, v___x_1969_);
if (v___x_1972_ == 0)
{
if (v___x_1970_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1966_, v_f_1962_, v_init_1963_);
return v___x_1973_;
}
else
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = lean_usize_of_nat(v___x_1969_);
lean_inc(v_f_1962_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1962_, v_buckets_1967_, v___x_1974_, v___x_1975_, v_init_1963_);
v___x_1977_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1966_, v_f_1962_, v___x_1976_);
return v___x_1977_;
}
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1969_);
lean_inc(v_f_1962_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1962_, v_buckets_1967_, v___x_1978_, v___x_1979_, v_init_1963_);
v___x_1981_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1966_, v_f_1962_, v___x_1980_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_1982_, lean_object* v_init_1983_, lean_object* v_m_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_1982_, v_init_1983_, v_m_1984_);
lean_dec_ref(v_m_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object* v_es_1986_, lean_object* v_a_1987_, lean_object* v_b_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1987_);
lean_ctor_set(v___x_1989_, 1, v_b_1988_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_es_1986_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object* v_m_1992_){
_start:
{
lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___f_1993_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0));
v___x_1994_ = lean_box(0);
v___x_1995_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_1993_, v___x_1994_, v_m_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object* v_m_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_1996_);
lean_dec_ref(v_m_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
if (lean_obj_tag(v_x_2000_) == 0)
{
lean_dec(v_x_1998_);
return v_x_1999_;
}
else
{
lean_object* v_head_2001_; lean_object* v_tail_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2011_; 
v_head_2001_ = lean_ctor_get(v_x_2000_, 0);
v_tail_2002_ = lean_ctor_get(v_x_2000_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_x_2000_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2004_ = v_x_2000_;
v_isShared_2005_ = v_isSharedCheck_2011_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_tail_2002_);
lean_inc(v_head_2001_);
lean_dec(v_x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2011_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
lean_inc(v_x_1998_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 5);
lean_ctor_set(v___x_2004_, 1, v_x_1998_);
lean_ctor_set(v___x_2004_, 0, v_x_1999_);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_x_1999_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_x_1998_);
v___x_2007_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v_head_2001_);
v_x_1999_ = v___x_2008_;
v_x_2000_ = v_tail_2002_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2012_) == 0)
{
lean_object* v___x_2014_; 
lean_dec(v_x_2013_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_tail_2015_; 
v_tail_2015_ = lean_ctor_get(v_x_2012_, 1);
if (lean_obj_tag(v_tail_2015_) == 0)
{
lean_object* v_head_2016_; 
lean_dec(v_x_2013_);
v_head_2016_ = lean_ctor_get(v_x_2012_, 0);
lean_inc(v_head_2016_);
lean_dec_ref_known(v_x_2012_, 2);
return v_head_2016_;
}
else
{
lean_object* v_head_2017_; lean_object* v___x_2018_; 
lean_inc(v_tail_2015_);
v_head_2017_ = lean_ctor_get(v_x_2012_, 0);
lean_inc(v_head_2017_);
lean_dec_ref_known(v_x_2012_, 2);
v___x_2018_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(v_x_2013_, v_head_2017_, v_tail_2015_);
return v___x_2018_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0));
v___x_2022_ = lean_string_length(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2);
v___x_2024_ = lean_nat_to_int(v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2029_){
_start:
{
lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2054_; 
v_fst_2030_ = lean_ctor_get(v_x_2029_, 0);
v_snd_2031_ = lean_ctor_get(v_x_2029_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_2029_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2033_ = v_x_2029_;
v_isShared_2034_ = v_isSharedCheck_2054_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_snd_2031_);
lean_inc(v_fst_2030_);
lean_dec(v_x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2054_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2035_ = lean_unbox(v_fst_2030_);
lean_dec(v_fst_2030_);
v___x_2036_ = l_Bool_repr___redArg(v___x_2035_);
v___x_2037_ = lean_box(0);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
lean_ctor_set(v___x_2033_, 1, v___x_2037_);
lean_ctor_set(v___x_2033_, 0, v___x_2036_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2040_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_snd_2031_);
v___x_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
v___x_2042_ = l_List_reverse___redArg(v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2044_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2042_, v___x_2043_);
v___x_2045_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2046_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v___x_2044_);
v___x_2048_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2045_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = 0;
v___x_2052_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*1, v___x_2051_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object* v_x_2055_){
_start:
{
lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2080_; 
v_fst_2056_ = lean_ctor_get(v_x_2055_, 0);
v_snd_2057_ = lean_ctor_get(v_x_2055_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_x_2055_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2059_ = v_x_2055_;
v_isShared_2060_ = v_isSharedCheck_2080_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_inc(v_fst_2056_);
lean_dec(v_x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2080_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_fst_2056_);
v___x_2063_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 1, v___x_2063_);
lean_ctor_set(v___x_2059_, 0, v___x_2062_);
v___x_2065_ = v___x_2059_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2066_ = l_Lean_Name_reprPrec(v_snd_2057_, v___x_2061_);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___x_2065_);
v___x_2068_ = l_List_reverse___redArg(v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2070_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2072_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2070_);
v___x_2074_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2071_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = 0;
v___x_2078_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*1, v___x_2077_);
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object* v_x_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
lean_dec(v_x_2081_);
return v_x_2082_;
}
else
{
lean_object* v_head_2084_; lean_object* v_tail_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2095_; 
v_head_2084_ = lean_ctor_get(v_x_2083_, 0);
v_tail_2085_ = lean_ctor_get(v_x_2083_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_x_2083_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2087_ = v_x_2083_;
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_tail_2085_);
lean_inc(v_head_2084_);
lean_dec(v_x_2083_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
lean_inc(v_x_2081_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 5);
lean_ctor_set(v___x_2087_, 1, v_x_2081_);
lean_ctor_set(v___x_2087_, 0, v_x_2082_);
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_x_2082_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_x_2081_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2084_);
v___x_2092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v_x_2082_ = v___x_2092_;
v_x_2083_ = v_tail_2085_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
if (lean_obj_tag(v_x_2098_) == 0)
{
lean_dec(v_x_2096_);
return v_x_2097_;
}
else
{
lean_object* v_head_2099_; lean_object* v_tail_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2110_; 
v_head_2099_ = lean_ctor_get(v_x_2098_, 0);
v_tail_2100_ = lean_ctor_get(v_x_2098_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2098_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2102_ = v_x_2098_;
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_tail_2100_);
lean_inc(v_head_2099_);
lean_dec(v_x_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
lean_inc(v_x_2096_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set_tag(v___x_2102_, 5);
lean_ctor_set(v___x_2102_, 1, v_x_2096_);
lean_ctor_set(v___x_2102_, 0, v_x_2097_);
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_x_2097_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_x_2096_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2099_);
v___x_2107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(v_x_2096_, v___x_2107_, v_tail_2100_);
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2113_; 
lean_dec(v_x_2112_);
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
else
{
lean_object* v_tail_2114_; 
v_tail_2114_ = lean_ctor_get(v_x_2111_, 1);
if (lean_obj_tag(v_tail_2114_) == 0)
{
lean_object* v_head_2115_; lean_object* v___x_2116_; 
lean_dec(v_x_2112_);
v_head_2115_ = lean_ctor_get(v_x_2111_, 0);
lean_inc(v_head_2115_);
lean_dec_ref_known(v_x_2111_, 2);
v___x_2116_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2115_);
return v___x_2116_;
}
else
{
lean_object* v_head_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_inc(v_tail_2114_);
v_head_2117_ = lean_ctor_get(v_x_2111_, 0);
lean_inc(v_head_2117_);
lean_dec_ref_known(v_x_2111_, 2);
v___x_2118_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2117_);
v___x_2119_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(v_x_2112_, v___x_2118_, v_tail_2114_);
return v___x_2119_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2));
v___x_2125_ = lean_string_length(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
v___x_2127_ = lean_nat_to_int(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1));
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2132_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2133_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_2130_, v___x_2132_);
v___x_2134_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
v___x_2135_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5));
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2133_);
v___x_2137_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2134_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = 0;
v___x_2141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
return v___x_2141_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_unsigned_to_nat(7u);
v___x_2152_ = lean_nat_to_int(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2157_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3));
v___x_2158_ = lean_obj_once(&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4, &l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_x_2156_);
v___x_2161_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_2160_);
v___x_2162_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6));
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Repr_addAppParen(v___x_2163_, v___x_2159_);
v___x_2165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2158_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = 0;
v___x_2167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2157_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_2170_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2168_);
v___x_2172_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2169_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*1, v___x_2166_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object* v_x_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2176_);
lean_dec_ref(v_x_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object* v_x_2178_, lean_object* v_prec_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object* v_x_2181_, lean_object* v_prec_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_2181_, v_prec_2182_);
lean_dec(v_prec_2182_);
lean_dec_ref(v_x_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object* v_00_u03b2_2184_, lean_object* v_m_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_m_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(v_00_u03b2_2187_, v_m_2188_);
lean_dec_ref(v_m_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object* v_a_2190_, lean_object* v_n_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object* v_a_2193_, lean_object* v_n_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_2193_, v_n_2194_);
lean_dec(v_n_2194_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object* v_00_u03b2_2196_, lean_object* v_00_u03c3_2197_, lean_object* v_f_2198_, lean_object* v_init_2199_, lean_object* v_m_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2198_, v_init_2199_, v_m_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2202_, lean_object* v_00_u03c3_2203_, lean_object* v_f_2204_, lean_object* v_init_2205_, lean_object* v_m_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_2202_, v_00_u03c3_2203_, v_f_2204_, v_init_2205_, v_m_2206_);
lean_dec_ref(v_m_2206_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_2211_, v_x_2212_);
lean_dec(v_x_2212_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2214_, lean_object* v_00_u03c3_2215_, lean_object* v_f_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_2216_, v_x_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2220_, lean_object* v_00_u03b2_2221_, lean_object* v_map_2222_, lean_object* v_f_2223_, lean_object* v_init_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_2222_, v_f_2223_, v_init_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_map_2228_, lean_object* v_f_2229_, lean_object* v_init_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_2226_, v_00_u03b2_2227_, v_map_2228_, v_f_2229_, v_init_2230_);
lean_dec_ref(v_map_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2232_, lean_object* v_00_u03c3_2233_, lean_object* v_f_2234_, lean_object* v_as_2235_, size_t v_i_2236_, size_t v_stop_2237_, lean_object* v_b_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_2234_, v_as_2235_, v_i_2236_, v_stop_2237_, v_b_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_00_u03c3_2241_, lean_object* v_f_2242_, lean_object* v_as_2243_, lean_object* v_i_2244_, lean_object* v_stop_2245_, lean_object* v_b_2246_){
_start:
{
size_t v_i_boxed_2247_; size_t v_stop_boxed_2248_; lean_object* v_res_2249_; 
v_i_boxed_2247_ = lean_unbox_usize(v_i_2244_);
lean_dec(v_i_2244_);
v_stop_boxed_2248_ = lean_unbox_usize(v_stop_2245_);
lean_dec(v_stop_2245_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(v_00_u03b2_2240_, v_00_u03c3_2241_, v_f_2242_, v_as_2243_, v_i_boxed_2247_, v_stop_boxed_2248_, v_b_2246_);
lean_dec_ref(v_as_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_x_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v_x_2253_, v_x_2254_);
lean_dec(v_x_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_map_2256_, lean_object* v_f_2257_, lean_object* v_init_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2257_, v_map_2256_, v_init_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_map_2260_, lean_object* v_f_2261_, lean_object* v_init_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_2260_, v_f_2261_, v_init_2262_);
lean_dec_ref(v_map_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03c3_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_map_2266_, lean_object* v_f_2267_, lean_object* v_init_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2267_, v_map_2266_, v_init_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03c3_2270_, lean_object* v_00_u03b2_2271_, lean_object* v_map_2272_, lean_object* v_f_2273_, lean_object* v_init_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_2270_, v_00_u03b2_2271_, v_map_2272_, v_f_2273_, v_init_2274_);
lean_dec_ref(v_map_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2276_, lean_object* v_00_u03b1_2277_, lean_object* v_00_u03b2_2278_, lean_object* v_f_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2279_, v_x_2280_, v_x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_f_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_2283_, v_00_u03b1_2284_, v_00_u03b2_2285_, v_f_2286_, v_x_2287_, v_x_2288_);
lean_dec_ref(v_x_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_2290_, lean_object* v_00_u03b2_2291_, lean_object* v_00_u03c3_2292_, lean_object* v_f_2293_, lean_object* v_as_2294_, size_t v_i_2295_, size_t v_stop_2296_, lean_object* v_b_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_2293_, v_as_2294_, v_i_2295_, v_stop_2296_, v_b_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_00_u03c3_2301_, lean_object* v_f_2302_, lean_object* v_as_2303_, lean_object* v_i_2304_, lean_object* v_stop_2305_, lean_object* v_b_2306_){
_start:
{
size_t v_i_boxed_2307_; size_t v_stop_boxed_2308_; lean_object* v_res_2309_; 
v_i_boxed_2307_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_stop_boxed_2308_ = lean_unbox_usize(v_stop_2305_);
lean_dec(v_stop_2305_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_2299_, v_00_u03b2_2300_, v_00_u03c3_2301_, v_f_2302_, v_as_2303_, v_i_boxed_2307_, v_stop_boxed_2308_, v_b_2306_);
lean_dec_ref(v_as_2303_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object* v_00_u03c3_2310_, lean_object* v_00_u03b1_2311_, lean_object* v_00_u03b2_2312_, lean_object* v_f_2313_, lean_object* v_keys_2314_, lean_object* v_vals_2315_, lean_object* v_heq_2316_, lean_object* v_i_2317_, lean_object* v_acc_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_2313_, v_keys_2314_, v_vals_2315_, v_i_2317_, v_acc_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object* v_00_u03c3_2320_, lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b2_2322_, lean_object* v_f_2323_, lean_object* v_keys_2324_, lean_object* v_vals_2325_, lean_object* v_heq_2326_, lean_object* v_i_2327_, lean_object* v_acc_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_2320_, v_00_u03b1_2321_, v_00_u03b2_2322_, v_f_2323_, v_keys_2324_, v_vals_2325_, v_heq_2326_, v_i_2327_, v_acc_2328_);
lean_dec_ref(v_vals_2325_);
lean_dec_ref(v_keys_2324_);
return v_res_2329_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2332_; uint64_t v___x_2333_; 
v___x_2332_ = lean_unsigned_to_nat(1723u);
v___x_2333_ = lean_uint64_of_nat(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object* v_as_2334_, size_t v_i_2335_, size_t v_stop_2336_, uint64_t v_b_2337_){
_start:
{
uint64_t v___y_2339_; uint8_t v___x_2344_; 
v___x_2344_ = lean_usize_dec_eq(v_i_2335_, v_stop_2336_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_array_uget_borrowed(v_as_2334_, v_i_2335_);
if (lean_obj_tag(v___x_2345_) == 0)
{
uint64_t v___x_2346_; 
v___x_2346_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0);
v___y_2339_ = v___x_2346_;
goto v___jp_2338_;
}
else
{
uint64_t v_hash_2347_; 
v_hash_2347_ = lean_ctor_get_uint64(v___x_2345_, sizeof(void*)*2);
v___y_2339_ = v_hash_2347_;
goto v___jp_2338_;
}
}
else
{
return v_b_2337_;
}
v___jp_2338_:
{
uint64_t v___x_2340_; size_t v___x_2341_; size_t v___x_2342_; 
v___x_2340_ = lean_uint64_mix_hash(v_b_2337_, v___y_2339_);
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2335_, v___x_2341_);
v_i_2335_ = v___x_2342_;
v_b_2337_ = v___x_2340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2348_, lean_object* v_i_2349_, lean_object* v_stop_2350_, lean_object* v_b_2351_){
_start:
{
size_t v_i_boxed_2352_; size_t v_stop_boxed_2353_; uint64_t v_b_boxed_2354_; uint64_t v_res_2355_; lean_object* v_r_2356_; 
v_i_boxed_2352_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_stop_boxed_2353_ = lean_unbox_usize(v_stop_2350_);
lean_dec(v_stop_2350_);
v_b_boxed_2354_ = lean_unbox_uint64(v_b_2351_);
lean_dec_ref(v_b_2351_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_2348_, v_i_boxed_2352_, v_stop_boxed_2353_, v_b_boxed_2354_);
lean_dec_ref(v_as_2348_);
v_r_2356_ = lean_box_uint64(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object* v_x_2357_, lean_object* v_x_2358_){
_start:
{
if (lean_obj_tag(v_x_2358_) == 0)
{
return v_x_2357_;
}
else
{
lean_object* v_key_2359_; lean_object* v_value_2360_; lean_object* v_tail_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2405_; 
v_key_2359_ = lean_ctor_get(v_x_2358_, 0);
v_value_2360_ = lean_ctor_get(v_x_2358_, 1);
v_tail_2361_ = lean_ctor_get(v_x_2358_, 2);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_x_2358_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2363_ = v_x_2358_;
v_isShared_2364_ = v_isSharedCheck_2405_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_tail_2361_);
lean_inc(v_value_2360_);
lean_inc(v_key_2359_);
lean_dec(v_x_2358_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2405_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_fst_2365_; lean_object* v_snd_2366_; lean_object* v___x_2367_; uint64_t v___y_2369_; uint64_t v___y_2370_; uint64_t v___y_2390_; uint8_t v___x_2402_; 
v_fst_2365_ = lean_ctor_get(v_key_2359_, 0);
v_snd_2366_ = lean_ctor_get(v_key_2359_, 1);
v___x_2367_ = lean_array_get_size(v_x_2357_);
v___x_2402_ = lean_unbox(v_fst_2365_);
if (v___x_2402_ == 0)
{
uint64_t v___x_2403_; 
v___x_2403_ = 13ULL;
v___y_2390_ = v___x_2403_;
goto v___jp_2389_;
}
else
{
uint64_t v___x_2404_; 
v___x_2404_ = 11ULL;
v___y_2390_ = v___x_2404_;
goto v___jp_2389_;
}
v___jp_2368_:
{
uint64_t v___x_2371_; uint64_t v___x_2372_; uint64_t v___x_2373_; uint64_t v_fold_2374_; uint64_t v___x_2375_; uint64_t v___x_2376_; uint64_t v___x_2377_; size_t v___x_2378_; size_t v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2371_ = lean_uint64_mix_hash(v___y_2369_, v___y_2370_);
v___x_2372_ = 32ULL;
v___x_2373_ = lean_uint64_shift_right(v___x_2371_, v___x_2372_);
v_fold_2374_ = lean_uint64_xor(v___x_2371_, v___x_2373_);
v___x_2375_ = 16ULL;
v___x_2376_ = lean_uint64_shift_right(v_fold_2374_, v___x_2375_);
v___x_2377_ = lean_uint64_xor(v_fold_2374_, v___x_2376_);
v___x_2378_ = lean_uint64_to_usize(v___x_2377_);
v___x_2379_ = lean_usize_of_nat(v___x_2367_);
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_sub(v___x_2379_, v___x_2380_);
v___x_2382_ = lean_usize_land(v___x_2378_, v___x_2381_);
v___x_2383_ = lean_array_uget_borrowed(v_x_2357_, v___x_2382_);
lean_inc(v___x_2383_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 2, v___x_2383_);
v___x_2385_ = v___x_2363_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_key_2359_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_value_2360_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_array_uset(v_x_2357_, v___x_2382_, v___x_2385_);
v_x_2357_ = v___x_2386_;
v_x_2358_ = v_tail_2361_;
goto _start;
}
}
v___jp_2389_:
{
uint64_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2391_ = 7ULL;
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_array_get_size(v_snd_2366_);
v___x_2394_ = lean_nat_dec_lt(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___x_2391_;
goto v___jp_2368_;
}
else
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_nat_dec_le(v___x_2393_, v___x_2393_);
if (v___x_2395_ == 0)
{
if (v___x_2394_ == 0)
{
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___x_2391_;
goto v___jp_2368_;
}
else
{
size_t v___x_2396_; size_t v___x_2397_; uint64_t v___x_2398_; 
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = lean_usize_of_nat(v___x_2393_);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2366_, v___x_2396_, v___x_2397_, v___x_2391_);
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___x_2398_;
goto v___jp_2368_;
}
}
else
{
size_t v___x_2399_; size_t v___x_2400_; uint64_t v___x_2401_; 
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = lean_usize_of_nat(v___x_2393_);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2366_, v___x_2399_, v___x_2400_, v___x_2391_);
v___y_2369_ = v___y_2390_;
v___y_2370_ = v___x_2401_;
goto v___jp_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_i_2406_, lean_object* v_source_2407_, lean_object* v_target_2408_){
_start:
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = lean_array_get_size(v_source_2407_);
v___x_2410_ = lean_nat_dec_lt(v_i_2406_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_dec_ref(v_source_2407_);
lean_dec(v_i_2406_);
return v_target_2408_;
}
else
{
lean_object* v_es_2411_; lean_object* v___x_2412_; lean_object* v_source_2413_; lean_object* v_target_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_es_2411_ = lean_array_fget(v_source_2407_, v_i_2406_);
v___x_2412_ = lean_box(0);
v_source_2413_ = lean_array_fset(v_source_2407_, v_i_2406_, v___x_2412_);
v_target_2414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_target_2408_, v_es_2411_);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_add(v_i_2406_, v___x_2415_);
lean_dec(v_i_2406_);
v_i_2406_ = v___x_2416_;
v_source_2407_ = v_source_2413_;
v_target_2408_ = v_target_2414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_data_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_nbuckets_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2419_ = lean_array_get_size(v_data_2418_);
v___x_2420_ = lean_unsigned_to_nat(2u);
v_nbuckets_2421_ = lean_nat_mul(v___x_2419_, v___x_2420_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_mk_array(v_nbuckets_2421_, v___x_2423_);
v___x_2425_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v___x_2422_, v_data_2418_, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_xs_2426_, lean_object* v_ys_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v_zero_2429_; uint8_t v_isZero_2430_; 
v_zero_2429_ = lean_unsigned_to_nat(0u);
v_isZero_2430_ = lean_nat_dec_eq(v_x_2428_, v_zero_2429_);
if (v_isZero_2430_ == 1)
{
lean_dec(v_x_2428_);
return v_isZero_2430_;
}
else
{
lean_object* v_one_2431_; lean_object* v_n_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_one_2431_ = lean_unsigned_to_nat(1u);
v_n_2432_ = lean_nat_sub(v_x_2428_, v_one_2431_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_array_fget_borrowed(v_xs_2426_, v_n_2432_);
v___x_2434_ = lean_array_fget_borrowed(v_ys_2427_, v_n_2432_);
v___x_2435_ = lean_name_eq(v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_dec(v_n_2432_);
return v___x_2435_;
}
else
{
v_x_2428_ = v_n_2432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_xs_2437_, lean_object* v_ys_2438_, lean_object* v_x_2439_){
_start:
{
uint8_t v_res_2440_; lean_object* v_r_2441_; 
v_res_2440_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2437_, v_ys_2438_, v_x_2439_);
lean_dec_ref(v_ys_2438_);
lean_dec_ref(v_xs_2437_);
v_r_2441_ = lean_box(v_res_2440_);
return v_r_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_a_2442_, lean_object* v_b_2443_, lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2444_) == 0)
{
lean_dec(v_b_2443_);
lean_dec_ref(v_a_2442_);
return v_x_2444_;
}
else
{
lean_object* v_key_2445_; lean_object* v_value_2446_; lean_object* v_tail_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2469_; 
v_key_2445_ = lean_ctor_get(v_x_2444_, 0);
v_value_2446_ = lean_ctor_get(v_x_2444_, 1);
v_tail_2447_ = lean_ctor_get(v_x_2444_, 2);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_x_2444_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2449_ = v_x_2444_;
v_isShared_2450_ = v_isSharedCheck_2469_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_tail_2447_);
lean_inc(v_value_2446_);
lean_inc(v_key_2445_);
lean_dec(v_x_2444_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2469_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; uint8_t v___x_2466_; 
v_fst_2456_ = lean_ctor_get(v_key_2445_, 0);
v_snd_2457_ = lean_ctor_get(v_key_2445_, 1);
v_fst_2458_ = lean_ctor_get(v_a_2442_, 0);
v_snd_2459_ = lean_ctor_get(v_a_2442_, 1);
v___x_2466_ = lean_unbox(v_fst_2456_);
if (v___x_2466_ == 0)
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_unbox(v_fst_2458_);
if (v___x_2467_ == 0)
{
goto v___jp_2460_;
}
else
{
goto v___jp_2451_;
}
}
else
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_unbox(v_fst_2458_);
if (v___x_2468_ == 0)
{
goto v___jp_2451_;
}
else
{
goto v___jp_2460_;
}
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2442_, v_b_2443_, v_tail_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 2, v___x_2452_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_key_2445_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_value_2446_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
v___jp_2460_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2461_ = lean_array_get_size(v_snd_2457_);
v___x_2462_ = lean_array_get_size(v_snd_2459_);
v___x_2463_ = lean_nat_dec_eq(v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
goto v___jp_2451_;
}
else
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2457_, v_snd_2459_, v___x_2461_);
if (v___x_2464_ == 0)
{
goto v___jp_2451_;
}
else
{
lean_object* v___x_2465_; 
lean_del_object(v___x_2449_);
lean_dec(v_value_2446_);
lean_dec(v_key_2445_);
v___x_2465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2442_);
lean_ctor_set(v___x_2465_, 1, v_b_2443_);
lean_ctor_set(v___x_2465_, 2, v_tail_2447_);
return v___x_2465_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_a_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = 0;
return v___x_2472_;
}
else
{
lean_object* v_key_2473_; lean_object* v_tail_2474_; lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; uint8_t v___x_2486_; 
v_key_2473_ = lean_ctor_get(v_x_2471_, 0);
v_tail_2474_ = lean_ctor_get(v_x_2471_, 2);
v_fst_2475_ = lean_ctor_get(v_key_2473_, 0);
v_snd_2476_ = lean_ctor_get(v_key_2473_, 1);
v_fst_2477_ = lean_ctor_get(v_a_2470_, 0);
v_snd_2478_ = lean_ctor_get(v_a_2470_, 1);
v___x_2486_ = lean_unbox(v_fst_2475_);
if (v___x_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_unbox(v_fst_2477_);
if (v___x_2487_ == 0)
{
goto v___jp_2479_;
}
else
{
v_x_2471_ = v_tail_2474_;
goto _start;
}
}
else
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_unbox(v_fst_2477_);
if (v___x_2489_ == 0)
{
v_x_2471_ = v_tail_2474_;
goto _start;
}
else
{
goto v___jp_2479_;
}
}
v___jp_2479_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = lean_array_get_size(v_snd_2476_);
v___x_2481_ = lean_array_get_size(v_snd_2478_);
v___x_2482_ = lean_nat_dec_eq(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
v_x_2471_ = v_tail_2474_;
goto _start;
}
else
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2476_, v_snd_2478_, v___x_2480_);
if (v___x_2484_ == 0)
{
v_x_2471_ = v_tail_2474_;
goto _start;
}
else
{
return v___x_2484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_a_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object* v_m_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v_size_2498_; lean_object* v_buckets_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2563_; 
v_size_2498_ = lean_ctor_get(v_m_2495_, 0);
v_buckets_2499_ = lean_ctor_get(v_m_2495_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_m_2495_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2501_ = v_m_2495_;
v_isShared_2502_ = v_isSharedCheck_2563_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_buckets_2499_);
lean_inc(v_size_2498_);
lean_dec(v_m_2495_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2563_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2505_; uint64_t v___y_2507_; uint64_t v___y_2508_; uint64_t v___y_2548_; uint8_t v___x_2560_; 
v_fst_2503_ = lean_ctor_get(v_a_2496_, 0);
v_snd_2504_ = lean_ctor_get(v_a_2496_, 1);
v___x_2505_ = lean_array_get_size(v_buckets_2499_);
v___x_2560_ = lean_unbox(v_fst_2503_);
if (v___x_2560_ == 0)
{
uint64_t v___x_2561_; 
v___x_2561_ = 13ULL;
v___y_2548_ = v___x_2561_;
goto v___jp_2547_;
}
else
{
uint64_t v___x_2562_; 
v___x_2562_ = 11ULL;
v___y_2548_ = v___x_2562_;
goto v___jp_2547_;
}
v___jp_2506_:
{
uint64_t v___x_2509_; uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v_fold_2512_; uint64_t v___x_2513_; uint64_t v___x_2514_; uint64_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; size_t v___x_2520_; lean_object* v_bkt_2521_; uint8_t v___x_2522_; 
v___x_2509_ = lean_uint64_mix_hash(v___y_2507_, v___y_2508_);
v___x_2510_ = 32ULL;
v___x_2511_ = lean_uint64_shift_right(v___x_2509_, v___x_2510_);
v_fold_2512_ = lean_uint64_xor(v___x_2509_, v___x_2511_);
v___x_2513_ = 16ULL;
v___x_2514_ = lean_uint64_shift_right(v_fold_2512_, v___x_2513_);
v___x_2515_ = lean_uint64_xor(v_fold_2512_, v___x_2514_);
v___x_2516_ = lean_uint64_to_usize(v___x_2515_);
v___x_2517_ = lean_usize_of_nat(v___x_2505_);
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_sub(v___x_2517_, v___x_2518_);
v___x_2520_ = lean_usize_land(v___x_2516_, v___x_2519_);
v_bkt_2521_ = lean_array_uget_borrowed(v_buckets_2499_, v___x_2520_);
v___x_2522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2496_, v_bkt_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v_size_x27_2524_; lean_object* v___x_2525_; lean_object* v_buckets_x27_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2523_ = lean_unsigned_to_nat(1u);
v_size_x27_2524_ = lean_nat_add(v_size_2498_, v___x_2523_);
lean_dec(v_size_2498_);
lean_inc(v_bkt_2521_);
v___x_2525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2525_, 0, v_a_2496_);
lean_ctor_set(v___x_2525_, 1, v_b_2497_);
lean_ctor_set(v___x_2525_, 2, v_bkt_2521_);
v_buckets_x27_2526_ = lean_array_uset(v_buckets_2499_, v___x_2520_, v___x_2525_);
v___x_2527_ = lean_unsigned_to_nat(4u);
v___x_2528_ = lean_nat_mul(v_size_x27_2524_, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(3u);
v___x_2530_ = lean_nat_div(v___x_2528_, v___x_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_array_get_size(v_buckets_x27_2526_);
v___x_2532_ = lean_nat_dec_le(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
if (v___x_2532_ == 0)
{
lean_object* v_val_2533_; lean_object* v___x_2535_; 
v_val_2533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_buckets_x27_2526_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_val_2533_);
lean_ctor_set(v___x_2501_, 0, v_size_x27_2524_);
v___x_2535_ = v___x_2501_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_size_x27_2524_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_val_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
else
{
lean_object* v___x_2538_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_buckets_x27_2526_);
lean_ctor_set(v___x_2501_, 0, v_size_x27_2524_);
v___x_2538_ = v___x_2501_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_size_x27_2524_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_buckets_x27_2526_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
else
{
lean_object* v___x_2540_; lean_object* v_buckets_x27_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_inc(v_bkt_2521_);
v___x_2540_ = lean_box(0);
v_buckets_x27_2541_ = lean_array_uset(v_buckets_2499_, v___x_2520_, v___x_2540_);
v___x_2542_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2496_, v_b_2497_, v_bkt_2521_);
v___x_2543_ = lean_array_uset(v_buckets_x27_2541_, v___x_2520_, v___x_2542_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2543_);
v___x_2545_ = v___x_2501_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_size_2498_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
v___jp_2547_:
{
uint64_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2549_ = 7ULL;
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = lean_array_get_size(v_snd_2504_);
v___x_2552_ = lean_nat_dec_lt(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
v___y_2507_ = v___y_2548_;
v___y_2508_ = v___x_2549_;
goto v___jp_2506_;
}
else
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_nat_dec_le(v___x_2551_, v___x_2551_);
if (v___x_2553_ == 0)
{
if (v___x_2552_ == 0)
{
v___y_2507_ = v___y_2548_;
v___y_2508_ = v___x_2549_;
goto v___jp_2506_;
}
else
{
size_t v___x_2554_; size_t v___x_2555_; uint64_t v___x_2556_; 
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2551_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2504_, v___x_2554_, v___x_2555_, v___x_2549_);
v___y_2507_ = v___y_2548_;
v___y_2508_ = v___x_2556_;
goto v___jp_2506_;
}
}
else
{
size_t v___x_2557_; size_t v___x_2558_; uint64_t v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2551_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2504_, v___x_2557_, v___x_2558_, v___x_2549_);
v___y_2507_ = v___y_2548_;
v___y_2508_ = v___x_2559_;
goto v___jp_2506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v_ks_2568_; lean_object* v_vs_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2608_; 
v_ks_2568_ = lean_ctor_get(v_x_2564_, 0);
v_vs_2569_ = lean_ctor_get(v_x_2564_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_x_2564_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2571_ = v_x_2564_;
v_isShared_2572_ = v_isSharedCheck_2608_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_vs_2569_);
lean_inc(v_ks_2568_);
lean_dec(v_x_2564_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2608_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = lean_array_get_size(v_ks_2568_);
v___x_2581_ = lean_nat_dec_lt(v_x_2565_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_del_object(v___x_2571_);
lean_dec(v_x_2565_);
v___x_2582_ = lean_array_push(v_ks_2568_, v_x_2566_);
v___x_2583_ = lean_array_push(v_vs_2569_, v_x_2567_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
return v___x_2584_;
}
else
{
lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v_k_x27_2587_; lean_object* v_fst_2588_; lean_object* v_snd_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2607_; 
v_fst_2585_ = lean_ctor_get(v_x_2566_, 0);
v_snd_2586_ = lean_ctor_get(v_x_2566_, 1);
v_k_x27_2587_ = lean_array_fget(v_ks_2568_, v_x_2565_);
v_fst_2588_ = lean_ctor_get(v_k_x27_2587_, 0);
v_snd_2589_ = lean_ctor_get(v_k_x27_2587_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_k_x27_2587_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2591_ = v_k_x27_2587_;
v_isShared_2592_ = v_isSharedCheck_2607_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_snd_2589_);
lean_inc(v_fst_2588_);
lean_dec(v_k_x27_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2607_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___y_2594_; uint8_t v___x_2604_; 
v___x_2604_ = lean_unbox(v_fst_2585_);
if (v___x_2604_ == 0)
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_unbox(v_fst_2588_);
lean_dec(v_fst_2588_);
if (v___x_2605_ == 0)
{
v___y_2594_ = v___x_2581_;
goto v___jp_2593_;
}
else
{
lean_del_object(v___x_2591_);
lean_dec(v_snd_2589_);
goto v___jp_2573_;
}
}
else
{
uint8_t v___x_2606_; 
v___x_2606_ = lean_unbox(v_fst_2588_);
lean_dec(v_fst_2588_);
v___y_2594_ = v___x_2606_;
goto v___jp_2593_;
}
v___jp_2593_:
{
if (v___y_2594_ == 0)
{
lean_del_object(v___x_2591_);
lean_dec(v_snd_2589_);
goto v___jp_2573_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2595_ = lean_array_get_size(v_snd_2586_);
v___x_2596_ = lean_array_get_size(v_snd_2589_);
v___x_2597_ = lean_nat_dec_eq(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_del_object(v___x_2591_);
lean_dec(v_snd_2589_);
goto v___jp_2573_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2586_, v_snd_2589_, v___x_2595_);
lean_dec(v_snd_2589_);
if (v___x_2598_ == 0)
{
lean_del_object(v___x_2591_);
goto v___jp_2573_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_del_object(v___x_2571_);
v___x_2599_ = lean_array_fset(v_ks_2568_, v_x_2565_, v_x_2566_);
v___x_2600_ = lean_array_fset(v_vs_2569_, v_x_2565_, v_x_2567_);
lean_dec(v_x_2565_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set_tag(v___x_2591_, 1);
lean_ctor_set(v___x_2591_, 1, v___x_2600_);
lean_ctor_set(v___x_2591_, 0, v___x_2599_);
v___x_2602_ = v___x_2591_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2575_; 
if (v_isShared_2572_ == 0)
{
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_ks_2568_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_vs_2569_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = lean_nat_add(v_x_2565_, v___x_2576_);
lean_dec(v_x_2565_);
v_x_2564_ = v___x_2575_;
v_x_2565_ = v___x_2577_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_2609_, lean_object* v_k_2610_, lean_object* v_v_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_n_2609_, v___x_2612_, v_k_2610_, v_v_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2615_, size_t v_x_2616_, size_t v_x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
if (lean_obj_tag(v_x_2615_) == 0)
{
lean_object* v_es_2620_; size_t v___x_2621_; size_t v___x_2622_; lean_object* v_j_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_es_2620_ = lean_ctor_get(v_x_2615_, 0);
v___x_2621_ = ((size_t)31ULL);
v___x_2622_ = lean_usize_land(v_x_2616_, v___x_2621_);
v_j_2623_ = lean_usize_to_nat(v___x_2622_);
v___x_2624_ = lean_array_get_size(v_es_2620_);
v___x_2625_ = lean_nat_dec_lt(v_j_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_dec(v_j_2623_);
lean_dec(v_x_2619_);
lean_dec_ref(v_x_2618_);
return v_x_2615_;
}
else
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2677_; 
lean_inc_ref(v_es_2620_);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2615_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_x_2615_, 0);
lean_dec(v_unused_2678_);
v___x_2627_ = v_x_2615_;
v_isShared_2628_ = v_isSharedCheck_2677_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v_x_2615_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2677_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v_v_2629_; lean_object* v___x_2630_; lean_object* v_xs_x27_2631_; lean_object* v___y_2633_; 
v_v_2629_ = lean_array_fget(v_es_2620_, v_j_2623_);
v___x_2630_ = lean_box(0);
v_xs_x27_2631_ = lean_array_fset(v_es_2620_, v_j_2623_, v___x_2630_);
switch(lean_obj_tag(v_v_2629_))
{
case 0:
{
lean_object* v_key_2638_; lean_object* v_val_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2662_; 
v_key_2638_ = lean_ctor_get(v_v_2629_, 0);
v_val_2639_ = lean_ctor_get(v_v_2629_, 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_v_2629_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2641_ = v_v_2629_;
v_isShared_2642_ = v_isSharedCheck_2662_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_val_2639_);
lean_inc(v_key_2638_);
lean_dec(v_v_2629_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2662_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v_fst_2648_; lean_object* v_snd_2649_; uint8_t v___y_2651_; uint8_t v___x_2659_; 
v_fst_2646_ = lean_ctor_get(v_x_2618_, 0);
v_snd_2647_ = lean_ctor_get(v_x_2618_, 1);
v_fst_2648_ = lean_ctor_get(v_key_2638_, 0);
v_snd_2649_ = lean_ctor_get(v_key_2638_, 1);
v___x_2659_ = lean_unbox(v_fst_2646_);
if (v___x_2659_ == 0)
{
uint8_t v___x_2660_; 
v___x_2660_ = lean_unbox(v_fst_2648_);
if (v___x_2660_ == 0)
{
v___y_2651_ = v___x_2625_;
goto v___jp_2650_;
}
else
{
lean_del_object(v___x_2641_);
goto v___jp_2643_;
}
}
else
{
uint8_t v___x_2661_; 
v___x_2661_ = lean_unbox(v_fst_2648_);
v___y_2651_ = v___x_2661_;
goto v___jp_2650_;
}
v___jp_2643_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2638_, v_val_2639_, v_x_2618_, v_x_2619_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
v___y_2633_ = v___x_2645_;
goto v___jp_2632_;
}
v___jp_2650_:
{
if (v___y_2651_ == 0)
{
lean_del_object(v___x_2641_);
goto v___jp_2643_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2652_ = lean_array_get_size(v_snd_2647_);
v___x_2653_ = lean_array_get_size(v_snd_2649_);
v___x_2654_ = lean_nat_dec_eq(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_del_object(v___x_2641_);
goto v___jp_2643_;
}
else
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2647_, v_snd_2649_, v___x_2652_);
if (v___x_2655_ == 0)
{
lean_del_object(v___x_2641_);
goto v___jp_2643_;
}
else
{
lean_object* v___x_2657_; 
lean_dec(v_val_2639_);
lean_dec(v_key_2638_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v_x_2619_);
lean_ctor_set(v___x_2641_, 0, v_x_2618_);
v___x_2657_ = v___x_2641_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_x_2618_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_x_2619_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
v___y_2633_ = v___x_2657_;
goto v___jp_2632_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_node_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2675_; 
v_node_2663_ = lean_ctor_get(v_v_2629_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_v_2629_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2665_ = v_v_2629_;
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_node_2663_);
lean_dec(v_v_2629_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
size_t v___x_2667_; size_t v___x_2668_; size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2667_ = ((size_t)5ULL);
v___x_2668_ = lean_usize_shift_right(v_x_2616_, v___x_2667_);
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_x_2617_, v___x_2669_);
v___x_2671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_node_2663_, v___x_2668_, v___x_2670_, v_x_2618_, v_x_2619_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2671_);
v___x_2673_ = v___x_2665_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
v___y_2633_ = v___x_2673_;
goto v___jp_2632_;
}
}
}
default: 
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_x_2618_);
lean_ctor_set(v___x_2676_, 1, v_x_2619_);
v___y_2633_ = v___x_2676_;
goto v___jp_2632_;
}
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_array_fset(v_xs_x27_2631_, v_j_2623_, v___y_2633_);
lean_dec(v_j_2623_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2634_);
v___x_2636_ = v___x_2627_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_ks_2679_; lean_object* v_vs_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2700_; 
v_ks_2679_ = lean_ctor_get(v_x_2615_, 0);
v_vs_2680_ = lean_ctor_get(v_x_2615_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_x_2615_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2682_ = v_x_2615_;
v_isShared_2683_ = v_isSharedCheck_2700_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_vs_2680_);
lean_inc(v_ks_2679_);
lean_dec(v_x_2615_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2700_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_ks_2679_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_vs_2680_);
v___x_2685_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v_newNode_2686_; uint8_t v___y_2688_; size_t v___x_2694_; uint8_t v___x_2695_; 
v_newNode_2686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v___x_2685_, v_x_2618_, v_x_2619_);
v___x_2694_ = ((size_t)7ULL);
v___x_2695_ = lean_usize_dec_le(v___x_2694_, v_x_2617_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2696_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2686_);
v___x_2697_ = lean_unsigned_to_nat(4u);
v___x_2698_ = lean_nat_dec_lt(v___x_2696_, v___x_2697_);
lean_dec(v___x_2696_);
v___y_2688_ = v___x_2698_;
goto v___jp_2687_;
}
else
{
v___y_2688_ = v___x_2695_;
goto v___jp_2687_;
}
v___jp_2687_:
{
if (v___y_2688_ == 0)
{
lean_object* v_ks_2689_; lean_object* v_vs_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_ks_2689_ = lean_ctor_get(v_newNode_2686_, 0);
lean_inc_ref(v_ks_2689_);
v_vs_2690_ = lean_ctor_get(v_newNode_2686_, 1);
lean_inc_ref(v_vs_2690_);
lean_dec_ref(v_newNode_2686_);
v___x_2691_ = lean_unsigned_to_nat(0u);
v___x_2692_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2693_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2617_, v_ks_2689_, v_vs_2690_, v___x_2691_, v___x_2692_);
lean_dec_ref(v_vs_2690_);
lean_dec_ref(v_ks_2689_);
return v___x_2693_;
}
else
{
return v_newNode_2686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_2701_, lean_object* v_keys_2702_, lean_object* v_vals_2703_, lean_object* v_i_2704_, lean_object* v_entries_2705_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = lean_array_get_size(v_keys_2702_);
v___x_2707_ = lean_nat_dec_lt(v_i_2704_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_dec(v_i_2704_);
return v_entries_2705_;
}
else
{
lean_object* v_k_2708_; lean_object* v_fst_2709_; lean_object* v_snd_2710_; lean_object* v_v_2711_; uint64_t v___y_2713_; uint64_t v___y_2714_; uint64_t v___y_2727_; uint8_t v___x_2739_; 
v_k_2708_ = lean_array_fget_borrowed(v_keys_2702_, v_i_2704_);
v_fst_2709_ = lean_ctor_get(v_k_2708_, 0);
v_snd_2710_ = lean_ctor_get(v_k_2708_, 1);
v_v_2711_ = lean_array_fget_borrowed(v_vals_2703_, v_i_2704_);
v___x_2739_ = lean_unbox(v_fst_2709_);
if (v___x_2739_ == 0)
{
uint64_t v___x_2740_; 
v___x_2740_ = 13ULL;
v___y_2727_ = v___x_2740_;
goto v___jp_2726_;
}
else
{
uint64_t v___x_2741_; 
v___x_2741_ = 11ULL;
v___y_2727_ = v___x_2741_;
goto v___jp_2726_;
}
v___jp_2712_:
{
uint64_t v___x_2715_; size_t v_h_2716_; size_t v___x_2717_; lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; size_t v_h_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2715_ = lean_uint64_mix_hash(v___y_2713_, v___y_2714_);
v_h_2716_ = lean_uint64_to_usize(v___x_2715_);
v___x_2717_ = ((size_t)5ULL);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_sub(v_depth_2701_, v___x_2719_);
v___x_2721_ = lean_usize_mul(v___x_2717_, v___x_2720_);
v_h_2722_ = lean_usize_shift_right(v_h_2716_, v___x_2721_);
v___x_2723_ = lean_nat_add(v_i_2704_, v___x_2718_);
lean_dec(v_i_2704_);
lean_inc(v_v_2711_);
lean_inc(v_k_2708_);
v___x_2724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_entries_2705_, v_h_2722_, v_depth_2701_, v_k_2708_, v_v_2711_);
v_i_2704_ = v___x_2723_;
v_entries_2705_ = v___x_2724_;
goto _start;
}
v___jp_2726_:
{
uint64_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2728_ = 7ULL;
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = lean_array_get_size(v_snd_2710_);
v___x_2731_ = lean_nat_dec_lt(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___x_2728_;
goto v___jp_2712_;
}
else
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_nat_dec_le(v___x_2730_, v___x_2730_);
if (v___x_2732_ == 0)
{
if (v___x_2731_ == 0)
{
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___x_2728_;
goto v___jp_2712_;
}
else
{
size_t v___x_2733_; size_t v___x_2734_; uint64_t v___x_2735_; 
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_of_nat(v___x_2730_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2710_, v___x_2733_, v___x_2734_, v___x_2728_);
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___x_2735_;
goto v___jp_2712_;
}
}
else
{
size_t v___x_2736_; size_t v___x_2737_; uint64_t v___x_2738_; 
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = lean_usize_of_nat(v___x_2730_);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2710_, v___x_2736_, v___x_2737_, v___x_2728_);
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___x_2738_;
goto v___jp_2712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_2742_, lean_object* v_keys_2743_, lean_object* v_vals_2744_, lean_object* v_i_2745_, lean_object* v_entries_2746_){
_start:
{
size_t v_depth_boxed_2747_; lean_object* v_res_2748_; 
v_depth_boxed_2747_ = lean_unbox_usize(v_depth_2742_);
lean_dec(v_depth_2742_);
v_res_2748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_2747_, v_keys_2743_, v_vals_2744_, v_i_2745_, v_entries_2746_);
lean_dec_ref(v_vals_2744_);
lean_dec_ref(v_keys_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
size_t v_x_2146__boxed_2754_; size_t v_x_2147__boxed_2755_; lean_object* v_res_2756_; 
v_x_2146__boxed_2754_ = lean_unbox_usize(v_x_2750_);
lean_dec(v_x_2750_);
v_x_2147__boxed_2755_ = lean_unbox_usize(v_x_2751_);
lean_dec(v_x_2751_);
v_res_2756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2749_, v_x_2146__boxed_2754_, v_x_2147__boxed_2755_, v_x_2752_, v_x_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
uint64_t v___y_2761_; uint64_t v___y_2762_; lean_object* v_fst_2767_; lean_object* v_snd_2768_; uint64_t v___y_2770_; uint8_t v___x_2782_; 
v_fst_2767_ = lean_ctor_get(v_x_2758_, 0);
v_snd_2768_ = lean_ctor_get(v_x_2758_, 1);
v___x_2782_ = lean_unbox(v_fst_2767_);
if (v___x_2782_ == 0)
{
uint64_t v___x_2783_; 
v___x_2783_ = 13ULL;
v___y_2770_ = v___x_2783_;
goto v___jp_2769_;
}
else
{
uint64_t v___x_2784_; 
v___x_2784_ = 11ULL;
v___y_2770_ = v___x_2784_;
goto v___jp_2769_;
}
v___jp_2760_:
{
uint64_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = lean_uint64_mix_hash(v___y_2761_, v___y_2762_);
v___x_2764_ = lean_uint64_to_usize(v___x_2763_);
v___x_2765_ = ((size_t)1ULL);
v___x_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2757_, v___x_2764_, v___x_2765_, v_x_2758_, v_x_2759_);
return v___x_2766_;
}
v___jp_2769_:
{
uint64_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2771_ = 7ULL;
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = lean_array_get_size(v_snd_2768_);
v___x_2774_ = lean_nat_dec_lt(v___x_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2771_;
goto v___jp_2760_;
}
else
{
uint8_t v___x_2775_; 
v___x_2775_ = lean_nat_dec_le(v___x_2773_, v___x_2773_);
if (v___x_2775_ == 0)
{
if (v___x_2774_ == 0)
{
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2771_;
goto v___jp_2760_;
}
else
{
size_t v___x_2776_; size_t v___x_2777_; uint64_t v___x_2778_; 
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = lean_usize_of_nat(v___x_2773_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2768_, v___x_2776_, v___x_2777_, v___x_2771_);
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2778_;
goto v___jp_2760_;
}
}
else
{
size_t v___x_2779_; size_t v___x_2780_; uint64_t v___x_2781_; 
v___x_2779_ = ((size_t)0ULL);
v___x_2780_ = lean_usize_of_nat(v___x_2773_);
v___x_2781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2768_, v___x_2779_, v___x_2780_, v___x_2771_);
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2781_;
goto v___jp_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_){
_start:
{
uint8_t v_stage_u2081_2788_; 
v_stage_u2081_2788_ = lean_ctor_get_uint8(v_x_2785_, sizeof(void*)*2);
if (v_stage_u2081_2788_ == 0)
{
lean_object* v_map_u2081_2789_; lean_object* v_map_u2082_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2798_; 
v_map_u2081_2789_ = lean_ctor_get(v_x_2785_, 0);
v_map_u2082_2790_ = lean_ctor_get(v_x_2785_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2792_ = v_x_2785_;
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_map_u2082_2790_);
lean_inc(v_map_u2081_2789_);
lean_dec(v_x_2785_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2082_2790_, v_x_2786_, v_x_2787_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2794_);
v___x_2796_ = v___x_2792_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_map_u2081_2789_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2797_, sizeof(void*)*2, v_stage_u2081_2788_);
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
lean_object* v_map_u2081_2799_; lean_object* v_map_u2082_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2808_; 
v_map_u2081_2799_ = lean_ctor_get(v_x_2785_, 0);
v_map_u2082_2800_ = lean_ctor_get(v_x_2785_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2802_ = v_x_2785_;
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_map_u2082_2800_);
lean_inc(v_map_u2081_2799_);
lean_dec(v_x_2785_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2081_2799_, v_x_2786_, v_x_2787_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_map_u2082_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2807_, sizeof(void*)*2, v_stage_u2081_2788_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* v_es_2809_, lean_object* v_e_2810_){
_start:
{
uint8_t v_induction_2811_; lean_object* v_typeNames_2812_; lean_object* v_elimName_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_induction_2811_ = lean_ctor_get_uint8(v_e_2810_, sizeof(void*)*2);
v_typeNames_2812_ = lean_ctor_get(v_e_2810_, 0);
lean_inc_ref(v_typeNames_2812_);
v_elimName_2813_ = lean_ctor_get(v_e_2810_, 1);
lean_inc(v_elimName_2813_);
lean_dec_ref(v_e_2810_);
v___x_2814_ = lean_box(v_induction_2811_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_typeNames_2812_);
v___x_2816_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_es_2809_, v___x_2815_, v_elimName_2813_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* v_00_u03b2_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_x_2818_, v_x_2819_, v_x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* v_00_u03b2_2822_, lean_object* v_x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_x_2823_, v_x_2824_, v_x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object* v_00_u03b2_2827_, lean_object* v_m_2828_, lean_object* v_a_2829_, lean_object* v_b_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_m_2828_, v_a_2829_, v_b_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2832_, lean_object* v_x_2833_, size_t v_x_2834_, size_t v_x_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2833_, v_x_2834_, v_x_2835_, v_x_2836_, v_x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
size_t v_x_2478__boxed_2845_; size_t v_x_2479__boxed_2846_; lean_object* v_res_2847_; 
v_x_2478__boxed_2845_ = lean_unbox_usize(v_x_2841_);
lean_dec(v_x_2841_);
v_x_2479__boxed_2846_ = lean_unbox_usize(v_x_2842_);
lean_dec(v_x_2842_);
v_res_2847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_2839_, v_x_2840_, v_x_2478__boxed_2845_, v_x_2479__boxed_2846_, v_x_2843_, v_x_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2848_, lean_object* v_a_2849_, lean_object* v_x_2850_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2849_, v_x_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2852_, lean_object* v_a_2853_, lean_object* v_x_2854_){
_start:
{
uint8_t v_res_2855_; lean_object* v_r_2856_; 
v_res_2855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_2852_, v_a_2853_, v_x_2854_);
lean_dec(v_x_2854_);
lean_dec_ref(v_a_2853_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2857_, lean_object* v_data_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_data_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_2860_, lean_object* v_a_2861_, lean_object* v_b_2862_, lean_object* v_x_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2861_, v_b_2862_, v_x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_2865_, lean_object* v_ys_2866_, lean_object* v_hsz_2867_, lean_object* v_x_2868_, lean_object* v_x_2869_){
_start:
{
uint8_t v___x_2870_; 
v___x_2870_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2865_, v_ys_2866_, v_x_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_2871_, lean_object* v_ys_2872_, lean_object* v_hsz_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_){
_start:
{
uint8_t v_res_2876_; lean_object* v_r_2877_; 
v_res_2876_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_2871_, v_ys_2872_, v_hsz_2873_, v_x_2874_, v_x_2875_);
lean_dec_ref(v_ys_2872_);
lean_dec_ref(v_xs_2871_);
v_r_2877_ = lean_box(v_res_2876_);
return v_r_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2878_, lean_object* v_n_2879_, lean_object* v_k_2880_, lean_object* v_v_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2879_, v_k_2880_, v_v_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2883_, size_t v_depth_2884_, lean_object* v_keys_2885_, lean_object* v_vals_2886_, lean_object* v_heq_2887_, lean_object* v_i_2888_, lean_object* v_entries_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_2884_, v_keys_2885_, v_vals_2886_, v_i_2888_, v_entries_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2891_, lean_object* v_depth_2892_, lean_object* v_keys_2893_, lean_object* v_vals_2894_, lean_object* v_heq_2895_, lean_object* v_i_2896_, lean_object* v_entries_2897_){
_start:
{
size_t v_depth_boxed_2898_; lean_object* v_res_2899_; 
v_depth_boxed_2898_ = lean_unbox_usize(v_depth_2892_);
lean_dec(v_depth_2892_);
v_res_2899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2891_, v_depth_boxed_2898_, v_keys_2893_, v_vals_2894_, v_heq_2895_, v_i_2896_, v_entries_2897_);
lean_dec_ref(v_vals_2894_);
lean_dec_ref(v_keys_2893_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2900_, lean_object* v_i_2901_, lean_object* v_source_2902_, lean_object* v_target_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v_i_2901_, v_source_2902_, v_target_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2906_, v_x_2907_, v_x_2908_, v_x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_x_2912_, v_x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_2915_){
_start:
{
uint8_t v_stage_u2081_2916_; 
v_stage_u2081_2916_ = lean_ctor_get_uint8(v_m_2915_, sizeof(void*)*2);
if (v_stage_u2081_2916_ == 0)
{
return v_m_2915_;
}
else
{
lean_object* v_map_u2081_2917_; lean_object* v_map_u2082_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
v_map_u2081_2917_ = lean_ctor_get(v_m_2915_, 0);
v_map_u2082_2918_ = lean_ctor_get(v_m_2915_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_m_2915_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2920_ = v_m_2915_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_map_u2082_2918_);
lean_inc(v_map_u2081_2917_);
lean_dec(v_m_2915_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
uint8_t v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = 0;
if (v_isShared_2921_ == 0)
{
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_map_u2081_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_map_u2082_2918_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*2, v___x_2922_);
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2927_, lean_object* v_m_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object* v_x_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2931_);
lean_inc_ref_n(v___x_2932_, 2);
v___x_2933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_x_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_2934_, v_a_2935_);
lean_dec_ref(v_x_2934_);
return v_res_2936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___f_2947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___f_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2949_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2950_);
lean_ctor_set(v___x_2952_, 2, v___x_2949_);
lean_ctor_set(v___x_2952_, 3, v___f_2948_);
lean_ctor_set(v___x_2952_, 4, v___f_2947_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
v___x_2955_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
return v_res_2957_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* v_x_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = 0;
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* v_x_2960_){
_start:
{
uint8_t v_res_2961_; lean_object* v_r_2962_; 
v_res_2961_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(v_x_2960_);
lean_dec(v_x_2960_);
v_r_2962_ = lean_box(v_res_2961_);
return v_r_2962_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* v_fvarId_2963_, lean_object* v_x_2964_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = l_Lean_instBEqFVarId_beq(v_fvarId_2963_, v_x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_2966_, lean_object* v_x_2967_){
_start:
{
uint8_t v_res_2968_; lean_object* v_r_2969_; 
v_res_2968_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(v_fvarId_2966_, v_x_2967_);
lean_dec(v_x_2967_);
lean_dec(v_fvarId_2966_);
v_r_2969_ = lean_box(v_res_2968_);
return v_r_2969_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_unsigned_to_nat(16u);
v___x_2973_ = lean_mk_array(v___x_2972_, v___x_2971_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* v_e_2977_, lean_object* v_fvarId_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; uint8_t v_fst_2983_; lean_object* v_mctx_2984_; lean_object* v_mctx_3001_; lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___y_3007_; uint8_t v___x_3014_; uint8_t v___x_3015_; 
v___x_2981_ = lean_st_ref_get(v___y_2979_);
v_mctx_3001_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref_n(v_mctx_3001_, 2);
lean_dec(v___x_2981_);
v___f_3002_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0));
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3003_, 0, v_fvarId_2978_);
v___x_3004_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v_mctx_3001_);
v___x_3014_ = l_Lean_Expr_hasFVar(v_e_2977_);
v___x_3015_ = lean_bool_not(v___x_3014_);
if (v___x_3015_ == 0)
{
v___y_3007_ = v___x_3015_;
goto v___jp_3006_;
}
else
{
uint8_t v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = l_Lean_Expr_hasMVar(v_e_2977_);
v___x_3017_ = lean_bool_not(v___x_3016_);
v___y_3007_ = v___x_3017_;
goto v___jp_3006_;
}
v___jp_2982_:
{
lean_object* v___x_2985_; lean_object* v_cache_2986_; lean_object* v_zetaDeltaFVarIds_2987_; lean_object* v_postponed_2988_; lean_object* v_diag_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2999_; 
v___x_2985_ = lean_st_ref_take(v___y_2979_);
v_cache_2986_ = lean_ctor_get(v___x_2985_, 1);
v_zetaDeltaFVarIds_2987_ = lean_ctor_get(v___x_2985_, 2);
v_postponed_2988_ = lean_ctor_get(v___x_2985_, 3);
v_diag_2989_ = lean_ctor_get(v___x_2985_, 4);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_3000_);
v___x_2991_ = v___x_2985_;
v_isShared_2992_ = v_isSharedCheck_2999_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_diag_2989_);
lean_inc(v_postponed_2988_);
lean_inc(v_zetaDeltaFVarIds_2987_);
lean_inc(v_cache_2986_);
lean_dec(v___x_2985_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2999_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v_mctx_2984_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_mctx_2984_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_cache_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_zetaDeltaFVarIds_2987_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_postponed_2988_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_diag_2989_);
v___x_2994_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_st_ref_set(v___y_2979_, v___x_2994_);
v___x_2996_ = lean_box(v_fst_2983_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
}
v___jp_3006_:
{
if (v___y_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v_snd_3009_; lean_object* v_fst_3010_; lean_object* v_mctx_3011_; uint8_t v___x_3012_; 
lean_dec_ref(v_mctx_3001_);
v___x_3008_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3003_, v___f_3002_, v_e_2977_, v___x_3005_);
v_snd_3009_ = lean_ctor_get(v___x_3008_, 1);
lean_inc(v_snd_3009_);
v_fst_3010_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_fst_3010_);
lean_dec_ref(v___x_3008_);
v_mctx_3011_ = lean_ctor_get(v_snd_3009_, 1);
lean_inc_ref(v_mctx_3011_);
lean_dec(v_snd_3009_);
v___x_3012_ = lean_unbox(v_fst_3010_);
lean_dec(v_fst_3010_);
v_fst_2983_ = v___x_3012_;
v_mctx_2984_ = v_mctx_3011_;
goto v___jp_2982_;
}
else
{
uint8_t v___x_3013_; 
lean_dec_ref_known(v___x_3005_, 2);
lean_dec_ref(v___f_3003_);
lean_dec_ref(v_e_2977_);
v___x_3013_ = 0;
v_fst_2983_ = v___x_3013_;
v_mctx_2984_ = v_mctx_3001_;
goto v___jp_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* v_e_3018_, lean_object* v_fvarId_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3018_, v_fvarId_3019_, v___y_3020_);
lean_dec(v___y_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object* v_e_3023_, lean_object* v_fvarId_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3023_, v_fvarId_3024_, v___y_3026_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* v_e_3031_, lean_object* v_fvarId_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(v_e_3031_, v_fvarId_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* v_upperBound_3042_, lean_object* v___x_3043_, lean_object* v_xs_3044_, lean_object* v___x_3045_, lean_object* v_a_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_nat_dec_lt(v_a_3046_, v_upperBound_3042_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_dec(v_a_3046_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_b_3047_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_b_3047_);
v___x_3055_ = l_Lean_instInhabitedExpr;
v___x_3056_ = lean_array_fget_borrowed(v___x_3043_, v_a_3046_);
v___x_3057_ = lean_array_get_borrowed(v___x_3055_, v_xs_3044_, v___x_3056_);
lean_inc(v___y_3051_);
lean_inc_ref(v___y_3050_);
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___x_3057_);
v___x_3058_ = lean_infer_type(v___x_3057_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_Lean_Expr_fvarId_x21(v___x_3045_);
v___x_3061_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_3059_, v___x_3060_, v___y_3049_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3077_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3077_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3077_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_unbox(v_a_3062_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_del_object(v___x_3064_);
lean_dec(v_a_3062_);
v___x_3068_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_add(v_a_3046_, v___x_3069_);
lean_dec(v_a_3046_);
v_a_3046_ = v___x_3070_;
v_b_3047_ = v___x_3068_;
goto _start;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_dec(v_a_3046_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_a_3062_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3066_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3073_);
v___x_3075_ = v___x_3064_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3046_);
v_a_3078_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3061_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3061_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3046_);
v_a_3086_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3058_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3058_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* v_upperBound_3094_, lean_object* v___x_3095_, lean_object* v_xs_3096_, lean_object* v___x_3097_, lean_object* v_a_3098_, lean_object* v_b_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3094_, v___x_3095_, v_xs_3096_, v___x_3097_, v_a_3098_, v_b_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___x_3097_);
lean_dec_ref(v_xs_3096_);
lean_dec_ref(v___x_3095_);
lean_dec(v_upperBound_3094_);
return v_res_3105_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* v_upperBound_3109_, lean_object* v___x_3110_, lean_object* v___x_3111_, lean_object* v_xs_3112_, lean_object* v_a_3113_, lean_object* v_b_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_a_3121_; uint8_t v___x_3125_; 
v___x_3125_ = lean_nat_dec_lt(v_a_3113_, v_upperBound_3109_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; 
lean_dec(v_a_3113_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_b_3114_);
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3127_ = l_Lean_instInhabitedExpr;
v___x_3128_ = lean_unsigned_to_nat(1u);
v___x_3129_ = lean_nat_add(v_a_3113_, v___x_3128_);
v___x_3130_ = lean_array_fget_borrowed(v___x_3111_, v_a_3113_);
v___x_3131_ = lean_array_get_borrowed(v___x_3127_, v_xs_3112_, v___x_3130_);
v___x_3158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_3110_, v___x_3111_, v_xs_3112_, v___x_3131_, v___x_3129_, v___x_3158_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_fst_3161_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v_fst_3161_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_fst_3161_);
lean_dec(v_a_3160_);
if (lean_obj_tag(v_fst_3161_) == 0)
{
goto v___jp_3132_;
}
else
{
lean_object* v_val_3162_; uint8_t v___x_3163_; 
v_val_3162_ = lean_ctor_get(v_fst_3161_, 0);
lean_inc(v_val_3162_);
lean_dec_ref_known(v_fst_3161_, 1);
v___x_3163_ = lean_unbox(v_val_3162_);
lean_dec(v_val_3162_);
if (v___x_3163_ == 0)
{
goto v___jp_3132_;
}
else
{
v_a_3121_ = v_b_3114_;
goto v___jp_3120_;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_b_3114_);
lean_dec(v_a_3113_);
v_a_3164_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3159_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3159_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
v___jp_3132_:
{
lean_object* v___x_3133_; 
lean_inc(v___y_3118_);
lean_inc_ref(v___y_3117_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3115_);
lean_inc(v___x_3131_);
v___x_3133_ = lean_infer_type(v___x_3131_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3135_ = l_Lean_Expr_getAppFn(v_a_3134_);
if (lean_obj_tag(v___x_3135_) == 4)
{
lean_object* v_declName_3136_; lean_object* v___x_3137_; 
lean_dec(v_a_3134_);
v_declName_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_declName_3136_);
lean_dec_ref_known(v___x_3135_, 2);
v___x_3137_ = lean_array_push(v_b_3114_, v_declName_3136_);
v_a_3121_ = v___x_3137_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec_ref(v___x_3135_);
v___x_3138_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
v___x_3139_ = l_Lean_indentExpr(v_a_3134_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_3140_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_dec_ref_known(v___x_3141_, 1);
v_a_3121_ = v_b_3114_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v_b_3114_);
lean_dec(v_a_3113_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
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
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_b_3114_);
lean_dec(v_a_3113_);
v_a_3150_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3133_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3133_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_nat_add(v_a_3113_, v___x_3122_);
lean_dec(v_a_3113_);
v_a_3113_ = v___x_3123_;
v_b_3114_ = v_a_3121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* v_upperBound_3172_, lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v_xs_3175_, lean_object* v_a_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3172_, v___x_3173_, v___x_3174_, v_xs_3175_, v_a_3176_, v_b_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec_ref(v_xs_3175_);
lean_dec_ref(v___x_3174_);
lean_dec(v___x_3173_);
lean_dec(v_upperBound_3172_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* v_a_3184_, uint8_t v_induction_3185_, lean_object* v_elimName_3186_, lean_object* v_xs_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_targetsPos_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_targetsPos_3194_ = lean_ctor_get(v_a_3184_, 3);
v___x_3195_ = lean_array_get_size(v_targetsPos_3194_);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_3198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_3195_, v___x_3195_, v_targetsPos_3194_, v_xs_3187_, v___x_3196_, v___x_3197_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3203_, 0, v_a_3199_);
lean_ctor_set(v___x_3203_, 1, v_elimName_3186_);
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*2, v_induction_3185_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_elimName_3186_);
v_a_3208_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3198_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3198_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* v_a_3216_, lean_object* v_induction_3217_, lean_object* v_elimName_3218_, lean_object* v_xs_3219_, lean_object* v_x_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v_induction_boxed_3226_; lean_object* v_res_3227_; 
v_induction_boxed_3226_ = lean_unbox(v_induction_3217_);
v_res_3227_ = l_Lean_Meta_mkCustomEliminator___lam__0(v_a_3216_, v_induction_boxed_3226_, v_elimName_3218_, v_xs_3219_, v_x_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v_x_3220_);
lean_dec_ref(v_xs_3219_);
lean_dec_ref(v_a_3216_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_3228_, lean_object* v_msg_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_fileName_3235_; lean_object* v_fileMap_3236_; lean_object* v_options_3237_; lean_object* v_currRecDepth_3238_; lean_object* v_maxRecDepth_3239_; lean_object* v_ref_3240_; lean_object* v_currNamespace_3241_; lean_object* v_openDecls_3242_; lean_object* v_initHeartbeats_3243_; lean_object* v_maxHeartbeats_3244_; lean_object* v_quotContext_3245_; lean_object* v_currMacroScope_3246_; uint8_t v_diag_3247_; lean_object* v_cancelTk_x3f_3248_; uint8_t v_suppressElabErrors_3249_; lean_object* v_inheritedTraceOptions_3250_; lean_object* v_ref_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_fileName_3235_ = lean_ctor_get(v___y_3232_, 0);
v_fileMap_3236_ = lean_ctor_get(v___y_3232_, 1);
v_options_3237_ = lean_ctor_get(v___y_3232_, 2);
v_currRecDepth_3238_ = lean_ctor_get(v___y_3232_, 3);
v_maxRecDepth_3239_ = lean_ctor_get(v___y_3232_, 4);
v_ref_3240_ = lean_ctor_get(v___y_3232_, 5);
v_currNamespace_3241_ = lean_ctor_get(v___y_3232_, 6);
v_openDecls_3242_ = lean_ctor_get(v___y_3232_, 7);
v_initHeartbeats_3243_ = lean_ctor_get(v___y_3232_, 8);
v_maxHeartbeats_3244_ = lean_ctor_get(v___y_3232_, 9);
v_quotContext_3245_ = lean_ctor_get(v___y_3232_, 10);
v_currMacroScope_3246_ = lean_ctor_get(v___y_3232_, 11);
v_diag_3247_ = lean_ctor_get_uint8(v___y_3232_, sizeof(void*)*14);
v_cancelTk_x3f_3248_ = lean_ctor_get(v___y_3232_, 12);
v_suppressElabErrors_3249_ = lean_ctor_get_uint8(v___y_3232_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3250_ = lean_ctor_get(v___y_3232_, 13);
v_ref_3251_ = l_Lean_replaceRef(v_ref_3228_, v_ref_3240_);
lean_inc_ref(v_inheritedTraceOptions_3250_);
lean_inc(v_cancelTk_x3f_3248_);
lean_inc(v_currMacroScope_3246_);
lean_inc(v_quotContext_3245_);
lean_inc(v_maxHeartbeats_3244_);
lean_inc(v_initHeartbeats_3243_);
lean_inc(v_openDecls_3242_);
lean_inc(v_currNamespace_3241_);
lean_inc(v_maxRecDepth_3239_);
lean_inc(v_currRecDepth_3238_);
lean_inc_ref(v_options_3237_);
lean_inc_ref(v_fileMap_3236_);
lean_inc_ref(v_fileName_3235_);
v___x_3252_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3252_, 0, v_fileName_3235_);
lean_ctor_set(v___x_3252_, 1, v_fileMap_3236_);
lean_ctor_set(v___x_3252_, 2, v_options_3237_);
lean_ctor_set(v___x_3252_, 3, v_currRecDepth_3238_);
lean_ctor_set(v___x_3252_, 4, v_maxRecDepth_3239_);
lean_ctor_set(v___x_3252_, 5, v_ref_3251_);
lean_ctor_set(v___x_3252_, 6, v_currNamespace_3241_);
lean_ctor_set(v___x_3252_, 7, v_openDecls_3242_);
lean_ctor_set(v___x_3252_, 8, v_initHeartbeats_3243_);
lean_ctor_set(v___x_3252_, 9, v_maxHeartbeats_3244_);
lean_ctor_set(v___x_3252_, 10, v_quotContext_3245_);
lean_ctor_set(v___x_3252_, 11, v_currMacroScope_3246_);
lean_ctor_set(v___x_3252_, 12, v_cancelTk_x3f_3248_);
lean_ctor_set(v___x_3252_, 13, v_inheritedTraceOptions_3250_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*14, v_diag_3247_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*14 + 1, v_suppressElabErrors_3249_);
v___x_3253_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_3229_, v___y_3230_, v___y_3231_, v___x_3252_, v___y_3233_);
lean_dec_ref_known(v___x_3252_, 14);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3254_, lean_object* v_msg_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3254_, v_msg_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v_ref_3254_);
return v_res_3261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
lean_ctor_set(v___x_3267_, 2, v___x_3266_);
lean_ctor_set(v___x_3267_, 3, v___x_3266_);
lean_ctor_set(v___x_3267_, 4, v___x_3265_);
lean_ctor_set(v___x_3267_, 5, v___x_3265_);
lean_ctor_set(v___x_3267_, 6, v___x_3265_);
lean_ctor_set(v___x_3267_, 7, v___x_3265_);
lean_ctor_set(v___x_3267_, 8, v___x_3265_);
lean_ctor_set(v___x_3267_, 9, v___x_3265_);
return v___x_3267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = lean_unsigned_to_nat(32u);
v___x_3269_ = lean_mk_empty_array_with_capacity(v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3271_ = ((size_t)5ULL);
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = lean_unsigned_to_nat(32u);
v___x_3274_ = lean_mk_empty_array_with_capacity(v___x_3273_);
v___x_3275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3276_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v___x_3274_);
lean_ctor_set(v___x_3276_, 2, v___x_3272_);
lean_ctor_set(v___x_3276_, 3, v___x_3272_);
lean_ctor_set_usize(v___x_3276_, 4, v___x_3271_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3277_ = lean_box(1);
v___x_3278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_3279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___x_3278_);
lean_ctor_set(v___x_3280_, 2, v___x_3277_);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_3298_ = l_Lean_stringToMessageData(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3302_, lean_object* v_declHint_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; lean_object* v_env_3307_; uint8_t v___y_3309_; uint8_t v___x_3365_; uint8_t v___x_3366_; 
v___x_3306_ = lean_st_ref_get(v___y_3304_);
v_env_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_ref(v_env_3307_);
lean_dec(v___x_3306_);
v___x_3365_ = l_Lean_Name_isAnonymous(v_declHint_3303_);
v___x_3366_ = lean_bool_not(v___x_3365_);
if (v___x_3366_ == 0)
{
v___y_3309_ = v___x_3366_;
goto v___jp_3308_;
}
else
{
uint8_t v_isExporting_3367_; 
v_isExporting_3367_ = lean_ctor_get_uint8(v_env_3307_, sizeof(void*)*8);
v___y_3309_ = v_isExporting_3367_;
goto v___jp_3308_;
}
v___jp_3308_:
{
if (v___y_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_dec_ref(v_env_3307_);
lean_dec(v_declHint_3303_);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_msg_3302_);
return v___x_3310_;
}
else
{
uint8_t v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3311_ = 0;
lean_inc_ref(v_env_3307_);
v___x_3312_ = l_Lean_Environment_setExporting(v_env_3307_, v___x_3311_);
lean_inc(v_declHint_3303_);
lean_inc_ref(v___x_3312_);
v___x_3313_ = l_Lean_Environment_contains(v___x_3312_, v_declHint_3303_, v___y_3309_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_env_3307_);
lean_dec(v_declHint_3303_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_msg_3302_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_c_3320_; lean_object* v___x_3321_; 
v___x_3315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3317_ = l_Lean_Options_empty;
v___x_3318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3312_);
lean_ctor_set(v___x_3318_, 1, v___x_3315_);
lean_ctor_set(v___x_3318_, 2, v___x_3316_);
lean_ctor_set(v___x_3318_, 3, v___x_3317_);
lean_inc(v_declHint_3303_);
v___x_3319_ = l_Lean_MessageData_ofConstName(v_declHint_3303_, v___x_3311_);
v_c_3320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3320_, 0, v___x_3318_);
lean_ctor_set(v_c_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3307_, v_declHint_3303_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec_ref(v_env_3307_);
lean_dec(v_declHint_3303_);
v___x_3322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v_c_3320_);
v___x_3324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = l_Lean_MessageData_note(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_msg_3302_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3364_; 
v_val_3329_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3331_ = v___x_3321_;
v_isShared_3332_ = v_isSharedCheck_3364_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_val_3329_);
lean_dec(v___x_3321_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3364_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v_mod_3336_; uint8_t v___x_3337_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lean_Environment_header(v_env_3307_);
lean_dec_ref(v_env_3307_);
v___x_3335_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3334_);
v_mod_3336_ = lean_array_get(v___x_3333_, v___x_3335_, v_val_3329_);
lean_dec(v_val_3329_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = l_Lean_isPrivateName(v_declHint_3303_);
lean_dec(v_declHint_3303_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
lean_ctor_set(v___x_3339_, 1, v_c_3320_);
v___x_3340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_MessageData_ofName(v_mod_3336_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_MessageData_note(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_msg_3302_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3347_);
v___x_3349_ = v___x_3331_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v_c_3320_);
v___x_3353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_MessageData_ofName(v_mod_3336_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Lean_MessageData_note(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_msg_3302_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3360_);
v___x_3362_ = v___x_3331_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3368_, lean_object* v_declHint_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3368_, v_declHint_3369_, v___y_3370_);
lean_dec(v___y_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3373_, lean_object* v_declHint_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3390_; 
v___x_3380_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3373_, v_declHint_3374_, v___y_3378_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3385_ = l_Lean_unknownIdentifierMessageTag;
v___x_3386_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v_a_3381_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3386_);
v___x_3388_ = v___x_3383_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3391_, lean_object* v_declHint_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3391_, v_declHint_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_3399_, lean_object* v_msg_3400_, lean_object* v_declHint_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; lean_object* v_a_3408_; lean_object* v___x_3409_; 
v___x_3407_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3400_, v_declHint_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3399_, v_a_3408_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_3410_, lean_object* v_msg_3411_, lean_object* v_declHint_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3410_, v_msg_3411_, v_declHint_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v_ref_3410_);
return v_res_3418_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3422_, lean_object* v_constName_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3429_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_3430_ = 0;
lean_inc(v_constName_3423_);
v___x_3431_ = l_Lean_MessageData_ofConstName(v_constName_3423_, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3422_, v___x_3434_, v_constName_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3436_, lean_object* v_constName_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3436_, v_constName_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v_ref_3436_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object* v_constName_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_ref_3450_; lean_object* v___x_3451_; 
v_ref_3450_ = lean_ctor_get(v___y_3447_, 5);
v___x_3451_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3450_, v_constName_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object* v_constName_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object* v_constName_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v_env_3466_; uint8_t v___x_3467_; lean_object* v___x_3468_; 
v___x_3465_ = lean_st_ref_get(v___y_3463_);
v_env_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc_ref(v_env_3466_);
lean_dec(v___x_3465_);
v___x_3467_ = 0;
lean_inc(v_constName_3459_);
v___x_3468_ = l_Lean_Environment_find_x3f(v_env_3466_, v_constName_3459_, v___x_3467_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3469_;
}
else
{
lean_object* v_val_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v_constName_3459_);
v_val_3470_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3468_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_val_3470_);
lean_dec(v___x_3468_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 0);
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_val_3470_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object* v_constName_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_constName_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* v_elimName_3485_, uint8_t v_induction_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_box(0);
lean_inc(v_elimName_3485_);
v___x_3493_ = l_Lean_Meta_getElimInfo(v_elimName_3485_, v___x_3492_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
lean_inc(v_elimName_3485_);
v___x_3495_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_elimName_3485_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___f_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = lean_box(v_induction_3486_);
v___f_3498_ = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3498_, 0, v_a_3494_);
lean_closure_set(v___f_3498_, 1, v___x_3497_);
lean_closure_set(v___f_3498_, 2, v_elimName_3485_);
v___x_3499_ = l_Lean_ConstantInfo_type(v_a_3496_);
lean_dec(v_a_3496_);
v___x_3500_ = 0;
v___x_3501_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_3499_, v___f_3498_, v___x_3500_, v___x_3500_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3501_;
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3494_);
lean_dec(v_elimName_3485_);
v_a_3502_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3495_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3495_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_elimName_3485_);
v_a_3510_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3493_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3493_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* v_elimName_3518_, lean_object* v_induction_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
uint8_t v_induction_boxed_3525_; lean_object* v_res_3526_; 
v_induction_boxed_3525_ = lean_unbox(v_induction_3519_);
v_res_3526_ = l_Lean_Meta_mkCustomEliminator(v_elimName_3518_, v_induction_boxed_3525_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object* v_upperBound_3527_, lean_object* v___x_3528_, lean_object* v_xs_3529_, lean_object* v___x_3530_, lean_object* v_inst_3531_, lean_object* v_R_3532_, lean_object* v_a_3533_, lean_object* v_b_3534_, lean_object* v_c_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3527_, v___x_3528_, v_xs_3529_, v___x_3530_, v_a_3533_, v_b_3534_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* v_upperBound_3542_, lean_object* v___x_3543_, lean_object* v_xs_3544_, lean_object* v___x_3545_, lean_object* v_inst_3546_, lean_object* v_R_3547_, lean_object* v_a_3548_, lean_object* v_b_3549_, lean_object* v_c_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(v_upperBound_3542_, v___x_3543_, v_xs_3544_, v___x_3545_, v_inst_3546_, v_R_3547_, v_a_3548_, v_b_3549_, v_c_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_xs_3544_);
lean_dec_ref(v___x_3543_);
lean_dec(v_upperBound_3542_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object* v_upperBound_3557_, lean_object* v___x_3558_, lean_object* v___x_3559_, lean_object* v_xs_3560_, lean_object* v_inst_3561_, lean_object* v_R_3562_, lean_object* v_a_3563_, lean_object* v_b_3564_, lean_object* v_c_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3557_, v___x_3558_, v___x_3559_, v_xs_3560_, v_a_3563_, v_b_3564_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* v_upperBound_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v_xs_3575_, lean_object* v_inst_3576_, lean_object* v_R_3577_, lean_object* v_a_3578_, lean_object* v_b_3579_, lean_object* v_c_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(v_upperBound_3572_, v___x_3573_, v___x_3574_, v_xs_3575_, v_inst_3576_, v_R_3577_, v_a_3578_, v_b_3579_, v_c_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v_xs_3575_);
lean_dec_ref(v___x_3574_);
lean_dec(v___x_3573_);
lean_dec(v_upperBound_3572_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object* v_00_u03b1_3587_, lean_object* v_constName_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_constName_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_3595_, v_constName_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3603_, lean_object* v_ref_3604_, lean_object* v_constName_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3604_, v_constName_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3612_, lean_object* v_ref_3613_, lean_object* v_constName_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_3612_, v_ref_3613_, v_constName_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v_ref_3613_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3621_, lean_object* v_ref_3622_, lean_object* v_msg_3623_, lean_object* v_declHint_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3622_, v_msg_3623_, v_declHint_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_ref_3632_, lean_object* v_msg_3633_, lean_object* v_declHint_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3631_, v_ref_3632_, v_msg_3633_, v_declHint_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_ref_3632_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object* v_msg_3641_, lean_object* v_declHint_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3641_, v_declHint_3642_, v___y_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3649_, lean_object* v_declHint_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_3649_, v_declHint_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_3657_, lean_object* v_ref_3658_, lean_object* v_msg_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3658_, v_msg_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_ref_3667_, lean_object* v_msg_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_3666_, v_ref_3667_, v_msg_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v_ref_3667_);
return v_res_3674_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3675_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
return v___x_3677_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
return v___x_3679_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3681_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
lean_ctor_set(v___x_3681_, 2, v___x_3680_);
lean_ctor_set(v___x_3681_, 3, v___x_3680_);
lean_ctor_set(v___x_3681_, 4, v___x_3680_);
lean_ctor_set(v___x_3681_, 5, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* v_ext_3682_, lean_object* v_b_3683_, uint8_t v_kind_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_currNamespace_3689_; lean_object* v___x_3690_; lean_object* v_env_3691_; lean_object* v_nextMacroScope_3692_; lean_object* v_ngen_3693_; lean_object* v_auxDeclNGen_3694_; lean_object* v_traceState_3695_; lean_object* v_messages_3696_; lean_object* v_infoState_3697_; lean_object* v_snapshotTasks_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3725_; 
v_currNamespace_3689_ = lean_ctor_get(v___y_3686_, 6);
v___x_3690_ = lean_st_ref_take(v___y_3687_);
v_env_3691_ = lean_ctor_get(v___x_3690_, 0);
v_nextMacroScope_3692_ = lean_ctor_get(v___x_3690_, 1);
v_ngen_3693_ = lean_ctor_get(v___x_3690_, 2);
v_auxDeclNGen_3694_ = lean_ctor_get(v___x_3690_, 3);
v_traceState_3695_ = lean_ctor_get(v___x_3690_, 4);
v_messages_3696_ = lean_ctor_get(v___x_3690_, 6);
v_infoState_3697_ = lean_ctor_get(v___x_3690_, 7);
v_snapshotTasks_3698_ = lean_ctor_get(v___x_3690_, 8);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; 
v_unused_3726_ = lean_ctor_get(v___x_3690_, 5);
lean_dec(v_unused_3726_);
v___x_3700_ = v___x_3690_;
v_isShared_3701_ = v_isSharedCheck_3725_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_snapshotTasks_3698_);
lean_inc(v_infoState_3697_);
lean_inc(v_messages_3696_);
lean_inc(v_traceState_3695_);
lean_inc(v_auxDeclNGen_3694_);
lean_inc(v_ngen_3693_);
lean_inc(v_nextMacroScope_3692_);
lean_inc(v_env_3691_);
lean_dec(v___x_3690_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3725_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
lean_inc(v_currNamespace_3689_);
v___x_3702_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3691_, v_ext_3682_, v_b_3683_, v_kind_3684_, v_currNamespace_3689_);
v___x_3703_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 5, v___x_3703_);
lean_ctor_set(v___x_3700_, 0, v___x_3702_);
v___x_3705_ = v___x_3700_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_nextMacroScope_3692_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_ngen_3693_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_auxDeclNGen_3694_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_traceState_3695_);
lean_ctor_set(v_reuseFailAlloc_3724_, 5, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3724_, 6, v_messages_3696_);
lean_ctor_set(v_reuseFailAlloc_3724_, 7, v_infoState_3697_);
lean_ctor_set(v_reuseFailAlloc_3724_, 8, v_snapshotTasks_3698_);
v___x_3705_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_mctx_3708_; lean_object* v_zetaDeltaFVarIds_3709_; lean_object* v_postponed_3710_; lean_object* v_diag_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3722_; 
v___x_3706_ = lean_st_ref_set(v___y_3687_, v___x_3705_);
v___x_3707_ = lean_st_ref_take(v___y_3685_);
v_mctx_3708_ = lean_ctor_get(v___x_3707_, 0);
v_zetaDeltaFVarIds_3709_ = lean_ctor_get(v___x_3707_, 2);
v_postponed_3710_ = lean_ctor_get(v___x_3707_, 3);
v_diag_3711_ = lean_ctor_get(v___x_3707_, 4);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v___x_3707_, 1);
lean_dec(v_unused_3723_);
v___x_3713_ = v___x_3707_;
v_isShared_3714_ = v_isSharedCheck_3722_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_diag_3711_);
lean_inc(v_postponed_3710_);
lean_inc(v_zetaDeltaFVarIds_3709_);
lean_inc(v_mctx_3708_);
lean_dec(v___x_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3722_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v___x_3715_);
v___x_3717_ = v___x_3713_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_mctx_3708_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_zetaDeltaFVarIds_3709_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_postponed_3710_);
lean_ctor_set(v_reuseFailAlloc_3721_, 4, v_diag_3711_);
v___x_3717_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_st_ref_set(v___y_3685_, v___x_3717_);
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* v_ext_3727_, lean_object* v_b_3728_, lean_object* v_kind_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_kind_boxed_3734_; lean_object* v_res_3735_; 
v_kind_boxed_3734_ = lean_unbox(v_kind_3729_);
v_res_3735_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3727_, v_b_3728_, v_kind_boxed_3734_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object* v_00_u03b1_3736_, lean_object* v_00_u03b2_3737_, lean_object* v_00_u03c3_3738_, lean_object* v_ext_3739_, lean_object* v_b_3740_, uint8_t v_kind_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3739_, v_b_3740_, v_kind_3741_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* v_00_u03b1_3748_, lean_object* v_00_u03b2_3749_, lean_object* v_00_u03c3_3750_, lean_object* v_ext_3751_, lean_object* v_b_3752_, lean_object* v_kind_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
uint8_t v_kind_boxed_3759_; lean_object* v_res_3760_; 
v_kind_boxed_3759_ = lean_unbox(v_kind_3753_);
v_res_3760_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(v_00_u03b1_3748_, v_00_u03b2_3749_, v_00_u03c3_3750_, v_ext_3751_, v_b_3752_, v_kind_boxed_3759_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* v_declName_3761_, uint8_t v_attrKind_3762_, uint8_t v_induction_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_Meta_mkCustomEliminator(v_declName_3761_, v_induction_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___x_3771_ = l_Lean_Meta_customEliminatorExt;
v___x_3772_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_3771_, v_a_3770_, v_attrKind_3762_, v_a_3765_, v_a_3766_, v_a_3767_);
return v___x_3772_;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3769_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3769_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* v_declName_3781_, lean_object* v_attrKind_3782_, lean_object* v_induction_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
uint8_t v_attrKind_boxed_3789_; uint8_t v_induction_boxed_3790_; lean_object* v_res_3791_; 
v_attrKind_boxed_3789_ = lean_unbox(v_attrKind_3782_);
v_induction_boxed_3790_ = lean_unbox(v_induction_3783_);
v_res_3791_ = l_Lean_Meta_addCustomEliminator(v_declName_3781_, v_attrKind_boxed_3789_, v_induction_boxed_3790_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
return v_res_3791_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3798_; uint64_t v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3798_);
return v___x_3799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3802_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set_uint64(v___x_3802_, sizeof(void*)*1, v___x_3800_);
return v___x_3802_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
return v___x_3805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
lean_ctor_set(v___x_3807_, 2, v___x_3806_);
lean_ctor_set(v___x_3807_, 3, v___x_3806_);
lean_ctor_set(v___x_3807_, 4, v___x_3806_);
lean_ctor_set(v___x_3807_, 5, v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
lean_ctor_set(v___x_3809_, 2, v___x_3808_);
lean_ctor_set(v___x_3809_, 3, v___x_3808_);
lean_ctor_set(v___x_3809_, 4, v___x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3810_, lean_object* v___x_3811_, lean_object* v_declName_3812_, lean_object* v_x_3813_, uint8_t v_attrKind_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
uint8_t v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; size_t v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3818_ = 1;
v___x_3819_ = 0;
v___x_3820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3822_ = lean_unsigned_to_nat(32u);
v___x_3823_ = lean_mk_empty_array_with_capacity(v___x_3822_);
v___x_3824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3825_ = ((size_t)5ULL);
lean_inc_n(v___x_3810_, 6);
v___x_3826_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3823_);
lean_ctor_set(v___x_3826_, 2, v___x_3810_);
lean_ctor_set(v___x_3826_, 3, v___x_3810_);
lean_ctor_set_usize(v___x_3826_, 4, v___x_3825_);
v___x_3827_ = lean_box(1);
lean_inc_ref(v___x_3826_);
v___x_3828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3821_);
lean_ctor_set(v___x_3828_, 1, v___x_3826_);
lean_ctor_set(v___x_3828_, 2, v___x_3827_);
v___x_3829_ = lean_mk_empty_array_with_capacity(v___x_3810_);
v___x_3830_ = lean_box(0);
lean_inc(v___x_3811_);
v___x_3831_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3831_, 0, v___x_3820_);
lean_ctor_set(v___x_3831_, 1, v___x_3811_);
lean_ctor_set(v___x_3831_, 2, v___x_3828_);
lean_ctor_set(v___x_3831_, 3, v___x_3829_);
lean_ctor_set(v___x_3831_, 4, v___x_3830_);
lean_ctor_set(v___x_3831_, 5, v___x_3810_);
lean_ctor_set(v___x_3831_, 6, v___x_3830_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*7, v___x_3819_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*7 + 1, v___x_3819_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*7 + 2, v___x_3819_);
lean_ctor_set_uint8(v___x_3831_, sizeof(void*)*7 + 3, v___x_3818_);
v___x_3832_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3810_);
lean_ctor_set(v___x_3832_, 1, v___x_3810_);
lean_ctor_set(v___x_3832_, 2, v___x_3810_);
lean_ctor_set(v___x_3832_, 3, v___x_3810_);
lean_ctor_set(v___x_3832_, 4, v___x_3821_);
lean_ctor_set(v___x_3832_, 5, v___x_3821_);
lean_ctor_set(v___x_3832_, 6, v___x_3821_);
lean_ctor_set(v___x_3832_, 7, v___x_3821_);
lean_ctor_set(v___x_3832_, 8, v___x_3821_);
lean_ctor_set(v___x_3832_, 9, v___x_3821_);
v___x_3833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3832_);
lean_ctor_set(v___x_3835_, 1, v___x_3833_);
lean_ctor_set(v___x_3835_, 2, v___x_3811_);
lean_ctor_set(v___x_3835_, 3, v___x_3826_);
lean_ctor_set(v___x_3835_, 4, v___x_3834_);
v___x_3836_ = lean_st_mk_ref(v___x_3835_);
v___x_3837_ = l_Lean_Meta_addCustomEliminator(v_declName_3812_, v_attrKind_3814_, v___x_3818_, v___x_3831_, v___x_3836_, v___y_3815_, v___y_3816_);
lean_dec_ref_known(v___x_3831_, 7);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3846_; 
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3837_, 0);
lean_dec(v_unused_3847_);
v___x_3839_ = v___x_3837_;
v_isShared_3840_ = v_isSharedCheck_3846_;
goto v_resetjp_3838_;
}
else
{
lean_dec(v___x_3837_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3846_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3841_ = lean_st_ref_get(v___x_3836_);
lean_dec(v___x_3836_);
lean_dec(v___x_3841_);
v___x_3842_ = lean_box(0);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3842_);
v___x_3844_ = v___x_3839_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v___x_3836_);
return v___x_3837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v_declName_3850_, lean_object* v_x_3851_, lean_object* v_attrKind_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
uint8_t v_attrKind_boxed_3856_; lean_object* v_res_3857_; 
v_attrKind_boxed_3856_ = lean_unbox(v_attrKind_3852_);
v_res_3857_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3848_, v___x_3849_, v_declName_3850_, v_x_3851_, v_attrKind_boxed_3856_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v_x_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; lean_object* v_env_3863_; lean_object* v_options_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3862_ = lean_st_ref_get(v___y_3860_);
v_env_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc_ref(v_env_3863_);
lean_dec(v___x_3862_);
v_options_3864_ = lean_ctor_get(v___y_3859_, 2);
v___x_3865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3866_ = lean_unsigned_to_nat(32u);
v___x_3867_ = lean_mk_empty_array_with_capacity(v___x_3866_);
lean_dec_ref(v___x_3867_);
v___x_3868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
lean_inc_ref(v_options_3864_);
v___x_3869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3869_, 0, v_env_3863_);
lean_ctor_set(v___x_3869_, 1, v___x_3865_);
lean_ctor_set(v___x_3869_, 2, v___x_3868_);
lean_ctor_set(v___x_3869_, 3, v_options_3864_);
v___x_3870_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v_msgData_3858_);
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_ref_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3891_; 
v_ref_3881_ = lean_ctor_get(v___y_3878_, 5);
v___x_3882_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_3877_, v___y_3878_, v___y_3879_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
lean_inc(v_ref_3881_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v_ref_3881_);
lean_ctor_set(v___x_3887_, 1, v_a_3883_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 1);
lean_ctor_set(v___x_3885_, 0, v___x_3887_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3892_, v___y_3893_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
return v_res_3896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3899_ = l_Lean_stringToMessageData(v___x_3898_);
return v___x_3899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3902_ = l_Lean_stringToMessageData(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3903_, lean_object* v_decl_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3909_ = l_Lean_MessageData_ofName(v___x_3903_);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3908_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3910_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_3912_, v___y_3905_, v___y_3906_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3914_, lean_object* v_decl_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3914_, v_decl_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v_decl_3915_);
return v_res_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = lean_unsigned_to_nat(2729305610u);
v___x_3971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3972_ = l_Lean_Name_num___override(v___x_3971_, v___x_3970_);
return v___x_3972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3976_ = l_Lean_Name_str___override(v___x_3975_, v___x_3974_);
return v___x_3976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3980_ = l_Lean_Name_str___override(v___x_3979_, v___x_3978_);
return v___x_3980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = lean_unsigned_to_nat(2u);
v___x_3982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3983_ = l_Lean_Name_num___override(v___x_3982_, v___x_3981_);
return v___x_3983_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3990_ = 0;
v___x_3991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3994_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v___x_3992_);
lean_ctor_set(v___x_3994_, 2, v___x_3991_);
lean_ctor_set_uint8(v___x_3994_, sizeof(void*)*3, v___x_3990_);
return v___x_3994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___f_3995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___f_3996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___f_3996_);
lean_ctor_set(v___x_3998_, 2, v___f_3995_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4001_ = l_Lean_registerBuiltinAttribute(v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_4004_, lean_object* v_msg_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_4005_, v___y_4006_, v___y_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_4010_, lean_object* v_msg_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_4010_, v_msg_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4020_ = l_Lean_addBuiltinDocString(v___x_4018_, v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4023_, lean_object* v___x_4024_, lean_object* v_declName_4025_, lean_object* v_x_4026_, uint8_t v_attrKind_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
uint8_t v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; size_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4031_ = 0;
v___x_4032_ = 1;
v___x_4033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4035_ = lean_unsigned_to_nat(32u);
v___x_4036_ = lean_mk_empty_array_with_capacity(v___x_4035_);
v___x_4037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_4038_ = ((size_t)5ULL);
lean_inc_n(v___x_4023_, 6);
v___x_4039_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4036_);
lean_ctor_set(v___x_4039_, 2, v___x_4023_);
lean_ctor_set(v___x_4039_, 3, v___x_4023_);
lean_ctor_set_usize(v___x_4039_, 4, v___x_4038_);
v___x_4040_ = lean_box(1);
lean_inc_ref(v___x_4039_);
v___x_4041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4034_);
lean_ctor_set(v___x_4041_, 1, v___x_4039_);
lean_ctor_set(v___x_4041_, 2, v___x_4040_);
v___x_4042_ = lean_mk_empty_array_with_capacity(v___x_4023_);
v___x_4043_ = lean_box(0);
lean_inc(v___x_4024_);
v___x_4044_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4044_, 0, v___x_4033_);
lean_ctor_set(v___x_4044_, 1, v___x_4024_);
lean_ctor_set(v___x_4044_, 2, v___x_4041_);
lean_ctor_set(v___x_4044_, 3, v___x_4042_);
lean_ctor_set(v___x_4044_, 4, v___x_4043_);
lean_ctor_set(v___x_4044_, 5, v___x_4023_);
lean_ctor_set(v___x_4044_, 6, v___x_4043_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*7, v___x_4031_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*7 + 1, v___x_4031_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*7 + 2, v___x_4031_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*7 + 3, v___x_4032_);
v___x_4045_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4023_);
lean_ctor_set(v___x_4045_, 1, v___x_4023_);
lean_ctor_set(v___x_4045_, 2, v___x_4023_);
lean_ctor_set(v___x_4045_, 3, v___x_4023_);
lean_ctor_set(v___x_4045_, 4, v___x_4034_);
lean_ctor_set(v___x_4045_, 5, v___x_4034_);
lean_ctor_set(v___x_4045_, 6, v___x_4034_);
lean_ctor_set(v___x_4045_, 7, v___x_4034_);
lean_ctor_set(v___x_4045_, 8, v___x_4034_);
lean_ctor_set(v___x_4045_, 9, v___x_4034_);
v___x_4046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4045_);
lean_ctor_set(v___x_4048_, 1, v___x_4046_);
lean_ctor_set(v___x_4048_, 2, v___x_4024_);
lean_ctor_set(v___x_4048_, 3, v___x_4039_);
lean_ctor_set(v___x_4048_, 4, v___x_4047_);
v___x_4049_ = lean_st_mk_ref(v___x_4048_);
v___x_4050_ = l_Lean_Meta_addCustomEliminator(v_declName_4025_, v_attrKind_4027_, v___x_4031_, v___x_4044_, v___x_4049_, v___y_4028_, v___y_4029_);
lean_dec_ref_known(v___x_4044_, 7);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4059_; 
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4059_ == 0)
{
lean_object* v_unused_4060_; 
v_unused_4060_ = lean_ctor_get(v___x_4050_, 0);
lean_dec(v_unused_4060_);
v___x_4052_ = v___x_4050_;
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
else
{
lean_dec(v___x_4050_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4054_ = lean_st_ref_get(v___x_4049_);
lean_dec(v___x_4049_);
lean_dec(v___x_4054_);
v___x_4055_ = lean_box(0);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4055_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
else
{
lean_dec(v___x_4049_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4061_, lean_object* v___x_4062_, lean_object* v_declName_4063_, lean_object* v_x_4064_, lean_object* v_attrKind_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
uint8_t v_attrKind_boxed_4069_; lean_object* v_res_4070_; 
v_attrKind_boxed_4069_ = lean_unbox(v_attrKind_4065_);
v_res_4070_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4061_, v___x_4062_, v_declName_4063_, v_x_4064_, v_attrKind_boxed_4069_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v_x_4064_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4071_, lean_object* v_decl_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4077_ = l_Lean_MessageData_ofName(v___x_4071_);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_4080_, v___y_4073_, v___y_4074_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4082_, lean_object* v_decl_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4082_, v_decl_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v_decl_4083_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4120_ = l_Lean_registerBuiltinAttribute(v___x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4127_ = l_Lean_addBuiltinDocString(v___x_4125_, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* v_a_4130_){
_start:
{
lean_object* v___x_4132_; lean_object* v_env_4133_; lean_object* v___x_4134_; lean_object* v_ext_4135_; lean_object* v_toEnvExtension_4136_; lean_object* v_asyncMode_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4132_ = lean_st_ref_get(v_a_4130_);
v_env_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc_ref(v_env_4133_);
lean_dec(v___x_4132_);
v___x_4134_ = l_Lean_Meta_customEliminatorExt;
v_ext_4135_ = lean_ctor_get(v___x_4134_, 1);
v_toEnvExtension_4136_ = lean_ctor_get(v_ext_4135_, 0);
v_asyncMode_4137_ = lean_ctor_get(v_toEnvExtension_4136_, 2);
v___x_4138_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4139_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4138_, v___x_4134_, v_env_4133_, v_asyncMode_4137_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4141_);
lean_dec(v_a_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4145_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_Meta_getCustomEliminators(v_a_4148_, v_a_4149_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_a_4152_, lean_object* v_x_4153_){
_start:
{
if (lean_obj_tag(v_x_4153_) == 0)
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_box(0);
return v___x_4154_;
}
else
{
lean_object* v_key_4155_; lean_object* v_value_4156_; lean_object* v_tail_4157_; lean_object* v_fst_4158_; lean_object* v_snd_4159_; lean_object* v_fst_4160_; lean_object* v_snd_4161_; uint8_t v___x_4170_; 
v_key_4155_ = lean_ctor_get(v_x_4153_, 0);
v_value_4156_ = lean_ctor_get(v_x_4153_, 1);
v_tail_4157_ = lean_ctor_get(v_x_4153_, 2);
v_fst_4158_ = lean_ctor_get(v_key_4155_, 0);
v_snd_4159_ = lean_ctor_get(v_key_4155_, 1);
v_fst_4160_ = lean_ctor_get(v_a_4152_, 0);
v_snd_4161_ = lean_ctor_get(v_a_4152_, 1);
v___x_4170_ = lean_unbox(v_fst_4158_);
if (v___x_4170_ == 0)
{
uint8_t v___x_4171_; 
v___x_4171_ = lean_unbox(v_fst_4160_);
if (v___x_4171_ == 0)
{
goto v___jp_4162_;
}
else
{
v_x_4153_ = v_tail_4157_;
goto _start;
}
}
else
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_unbox(v_fst_4160_);
if (v___x_4173_ == 0)
{
v_x_4153_ = v_tail_4157_;
goto _start;
}
else
{
goto v___jp_4162_;
}
}
v___jp_4162_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4163_ = lean_array_get_size(v_snd_4159_);
v___x_4164_ = lean_array_get_size(v_snd_4161_);
v___x_4165_ = lean_nat_dec_eq(v___x_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
v_x_4153_ = v_tail_4157_;
goto _start;
}
else
{
uint8_t v___x_4167_; 
v___x_4167_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4159_, v_snd_4161_, v___x_4163_);
if (v___x_4167_ == 0)
{
v_x_4153_ = v_tail_4157_;
goto _start;
}
else
{
lean_object* v___x_4169_; 
lean_inc(v_value_4156_);
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_value_4156_);
return v___x_4169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4175_, v_x_4176_);
lean_dec(v_x_4176_);
lean_dec_ref(v_a_4175_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object* v_m_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v_buckets_4180_; lean_object* v_fst_4181_; lean_object* v_snd_4182_; lean_object* v___x_4183_; uint64_t v___y_4185_; uint64_t v___y_4186_; uint64_t v___y_4202_; uint8_t v___x_4214_; 
v_buckets_4180_ = lean_ctor_get(v_m_4178_, 1);
v_fst_4181_ = lean_ctor_get(v_a_4179_, 0);
v_snd_4182_ = lean_ctor_get(v_a_4179_, 1);
v___x_4183_ = lean_array_get_size(v_buckets_4180_);
v___x_4214_ = lean_unbox(v_fst_4181_);
if (v___x_4214_ == 0)
{
uint64_t v___x_4215_; 
v___x_4215_ = 13ULL;
v___y_4202_ = v___x_4215_;
goto v___jp_4201_;
}
else
{
uint64_t v___x_4216_; 
v___x_4216_ = 11ULL;
v___y_4202_ = v___x_4216_;
goto v___jp_4201_;
}
v___jp_4184_:
{
uint64_t v___x_4187_; uint64_t v___x_4188_; uint64_t v___x_4189_; uint64_t v_fold_4190_; uint64_t v___x_4191_; uint64_t v___x_4192_; uint64_t v___x_4193_; size_t v___x_4194_; size_t v___x_4195_; size_t v___x_4196_; size_t v___x_4197_; size_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4187_ = lean_uint64_mix_hash(v___y_4185_, v___y_4186_);
v___x_4188_ = 32ULL;
v___x_4189_ = lean_uint64_shift_right(v___x_4187_, v___x_4188_);
v_fold_4190_ = lean_uint64_xor(v___x_4187_, v___x_4189_);
v___x_4191_ = 16ULL;
v___x_4192_ = lean_uint64_shift_right(v_fold_4190_, v___x_4191_);
v___x_4193_ = lean_uint64_xor(v_fold_4190_, v___x_4192_);
v___x_4194_ = lean_uint64_to_usize(v___x_4193_);
v___x_4195_ = lean_usize_of_nat(v___x_4183_);
v___x_4196_ = ((size_t)1ULL);
v___x_4197_ = lean_usize_sub(v___x_4195_, v___x_4196_);
v___x_4198_ = lean_usize_land(v___x_4194_, v___x_4197_);
v___x_4199_ = lean_array_uget_borrowed(v_buckets_4180_, v___x_4198_);
v___x_4200_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4179_, v___x_4199_);
return v___x_4200_;
}
v___jp_4201_:
{
uint64_t v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4203_ = 7ULL;
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = lean_array_get_size(v_snd_4182_);
v___x_4206_ = lean_nat_dec_lt(v___x_4204_, v___x_4205_);
if (v___x_4206_ == 0)
{
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___x_4203_;
goto v___jp_4184_;
}
else
{
uint8_t v___x_4207_; 
v___x_4207_ = lean_nat_dec_le(v___x_4205_, v___x_4205_);
if (v___x_4207_ == 0)
{
if (v___x_4206_ == 0)
{
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___x_4203_;
goto v___jp_4184_;
}
else
{
size_t v___x_4208_; size_t v___x_4209_; uint64_t v___x_4210_; 
v___x_4208_ = ((size_t)0ULL);
v___x_4209_ = lean_usize_of_nat(v___x_4205_);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4182_, v___x_4208_, v___x_4209_, v___x_4203_);
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___x_4210_;
goto v___jp_4184_;
}
}
else
{
size_t v___x_4211_; size_t v___x_4212_; uint64_t v___x_4213_; 
v___x_4211_ = ((size_t)0ULL);
v___x_4212_ = lean_usize_of_nat(v___x_4205_);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4182_, v___x_4211_, v___x_4212_, v___x_4203_);
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___x_4213_;
goto v___jp_4184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_m_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4217_, v_a_4218_);
lean_dec_ref(v_a_4218_);
lean_dec_ref(v_m_4217_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_4220_, lean_object* v_vals_4221_, lean_object* v_i_4222_, lean_object* v_k_4223_){
_start:
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4228_ = lean_array_get_size(v_keys_4220_);
v___x_4229_ = lean_nat_dec_lt(v_i_4222_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; 
lean_dec(v_i_4222_);
v___x_4230_ = lean_box(0);
return v___x_4230_;
}
else
{
lean_object* v_fst_4231_; lean_object* v_snd_4232_; lean_object* v_k_x27_4233_; lean_object* v_fst_4234_; lean_object* v_snd_4235_; uint8_t v___y_4237_; uint8_t v___x_4244_; 
v_fst_4231_ = lean_ctor_get(v_k_4223_, 0);
v_snd_4232_ = lean_ctor_get(v_k_4223_, 1);
v_k_x27_4233_ = lean_array_fget_borrowed(v_keys_4220_, v_i_4222_);
v_fst_4234_ = lean_ctor_get(v_k_x27_4233_, 0);
v_snd_4235_ = lean_ctor_get(v_k_x27_4233_, 1);
v___x_4244_ = lean_unbox(v_fst_4231_);
if (v___x_4244_ == 0)
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_unbox(v_fst_4234_);
if (v___x_4245_ == 0)
{
v___y_4237_ = v___x_4229_;
goto v___jp_4236_;
}
else
{
goto v___jp_4224_;
}
}
else
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_unbox(v_fst_4234_);
v___y_4237_ = v___x_4246_;
goto v___jp_4236_;
}
v___jp_4236_:
{
if (v___y_4237_ == 0)
{
goto v___jp_4224_;
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v___x_4238_ = lean_array_get_size(v_snd_4232_);
v___x_4239_ = lean_array_get_size(v_snd_4235_);
v___x_4240_ = lean_nat_dec_eq(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
goto v___jp_4224_;
}
else
{
uint8_t v___x_4241_; 
v___x_4241_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4232_, v_snd_4235_, v___x_4238_);
if (v___x_4241_ == 0)
{
goto v___jp_4224_;
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_array_fget_borrowed(v_vals_4221_, v_i_4222_);
lean_dec(v_i_4222_);
lean_inc(v___x_4242_);
v___x_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
return v___x_4243_;
}
}
}
}
}
v___jp_4224_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_nat_add(v_i_4222_, v___x_4225_);
lean_dec(v_i_4222_);
v_i_4222_ = v___x_4226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_4247_, lean_object* v_vals_4248_, lean_object* v_i_4249_, lean_object* v_k_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4247_, v_vals_4248_, v_i_4249_, v_k_4250_);
lean_dec_ref(v_k_4250_);
lean_dec_ref(v_vals_4248_);
lean_dec_ref(v_keys_4247_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_4252_, size_t v_x_4253_, lean_object* v_x_4254_){
_start:
{
if (lean_obj_tag(v_x_4252_) == 0)
{
lean_object* v_es_4255_; lean_object* v___x_4256_; size_t v___x_4257_; size_t v___x_4258_; lean_object* v_j_4259_; lean_object* v___x_4260_; 
v_es_4255_ = lean_ctor_get(v_x_4252_, 0);
v___x_4256_ = lean_box(2);
v___x_4257_ = ((size_t)31ULL);
v___x_4258_ = lean_usize_land(v_x_4253_, v___x_4257_);
v_j_4259_ = lean_usize_to_nat(v___x_4258_);
v___x_4260_ = lean_array_get_borrowed(v___x_4256_, v_es_4255_, v_j_4259_);
lean_dec(v_j_4259_);
switch(lean_obj_tag(v___x_4260_))
{
case 0:
{
lean_object* v_key_4261_; lean_object* v_val_4262_; lean_object* v_fst_4263_; lean_object* v_snd_4264_; lean_object* v_fst_4265_; lean_object* v_snd_4266_; uint8_t v___x_4275_; 
v_key_4261_ = lean_ctor_get(v___x_4260_, 0);
v_val_4262_ = lean_ctor_get(v___x_4260_, 1);
v_fst_4263_ = lean_ctor_get(v_x_4254_, 0);
v_snd_4264_ = lean_ctor_get(v_x_4254_, 1);
v_fst_4265_ = lean_ctor_get(v_key_4261_, 0);
v_snd_4266_ = lean_ctor_get(v_key_4261_, 1);
v___x_4275_ = lean_unbox(v_fst_4263_);
if (v___x_4275_ == 0)
{
uint8_t v___x_4276_; 
v___x_4276_ = lean_unbox(v_fst_4265_);
if (v___x_4276_ == 0)
{
goto v___jp_4267_;
}
else
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_box(0);
return v___x_4277_;
}
}
else
{
uint8_t v___x_4278_; 
v___x_4278_ = lean_unbox(v_fst_4265_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_box(0);
return v___x_4279_;
}
else
{
goto v___jp_4267_;
}
}
v___jp_4267_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_array_get_size(v_snd_4264_);
v___x_4269_ = lean_array_get_size(v_snd_4266_);
v___x_4270_ = lean_nat_dec_eq(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_box(0);
return v___x_4271_;
}
else
{
uint8_t v___x_4272_; 
v___x_4272_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4264_, v_snd_4266_, v___x_4268_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; 
v___x_4273_ = lean_box(0);
return v___x_4273_;
}
else
{
lean_object* v___x_4274_; 
lean_inc(v_val_4262_);
v___x_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4274_, 0, v_val_4262_);
return v___x_4274_;
}
}
}
}
case 1:
{
lean_object* v_node_4280_; size_t v___x_4281_; size_t v___x_4282_; 
v_node_4280_ = lean_ctor_get(v___x_4260_, 0);
v___x_4281_ = ((size_t)5ULL);
v___x_4282_ = lean_usize_shift_right(v_x_4253_, v___x_4281_);
v_x_4252_ = v_node_4280_;
v_x_4253_ = v___x_4282_;
goto _start;
}
default: 
{
lean_object* v___x_4284_; 
v___x_4284_ = lean_box(0);
return v___x_4284_;
}
}
}
else
{
lean_object* v_ks_4285_; lean_object* v_vs_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_ks_4285_ = lean_ctor_get(v_x_4252_, 0);
v_vs_4286_ = lean_ctor_get(v_x_4252_, 1);
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_4285_, v_vs_4286_, v___x_4287_, v_x_4254_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
size_t v_x_2269__boxed_4292_; lean_object* v_res_4293_; 
v_x_2269__boxed_4292_ = lean_unbox_usize(v_x_4290_);
lean_dec(v_x_4290_);
v_res_4293_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4289_, v_x_2269__boxed_4292_, v_x_4291_);
lean_dec_ref(v_x_4291_);
lean_dec_ref(v_x_4289_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
uint64_t v___y_4297_; uint64_t v___y_4298_; lean_object* v_fst_4302_; lean_object* v_snd_4303_; uint64_t v___y_4305_; uint8_t v___x_4317_; 
v_fst_4302_ = lean_ctor_get(v_x_4295_, 0);
v_snd_4303_ = lean_ctor_get(v_x_4295_, 1);
v___x_4317_ = lean_unbox(v_fst_4302_);
if (v___x_4317_ == 0)
{
uint64_t v___x_4318_; 
v___x_4318_ = 13ULL;
v___y_4305_ = v___x_4318_;
goto v___jp_4304_;
}
else
{
uint64_t v___x_4319_; 
v___x_4319_ = 11ULL;
v___y_4305_ = v___x_4319_;
goto v___jp_4304_;
}
v___jp_4296_:
{
uint64_t v___x_4299_; size_t v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_uint64_mix_hash(v___y_4297_, v___y_4298_);
v___x_4300_ = lean_uint64_to_usize(v___x_4299_);
v___x_4301_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4294_, v___x_4300_, v_x_4295_);
return v___x_4301_;
}
v___jp_4304_:
{
uint64_t v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4306_ = 7ULL;
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_array_get_size(v_snd_4303_);
v___x_4309_ = lean_nat_dec_lt(v___x_4307_, v___x_4308_);
if (v___x_4309_ == 0)
{
v___y_4297_ = v___y_4305_;
v___y_4298_ = v___x_4306_;
goto v___jp_4296_;
}
else
{
uint8_t v___x_4310_; 
v___x_4310_ = lean_nat_dec_le(v___x_4308_, v___x_4308_);
if (v___x_4310_ == 0)
{
if (v___x_4309_ == 0)
{
v___y_4297_ = v___y_4305_;
v___y_4298_ = v___x_4306_;
goto v___jp_4296_;
}
else
{
size_t v___x_4311_; size_t v___x_4312_; uint64_t v___x_4313_; 
v___x_4311_ = ((size_t)0ULL);
v___x_4312_ = lean_usize_of_nat(v___x_4308_);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4303_, v___x_4311_, v___x_4312_, v___x_4306_);
v___y_4297_ = v___y_4305_;
v___y_4298_ = v___x_4313_;
goto v___jp_4296_;
}
}
else
{
size_t v___x_4314_; size_t v___x_4315_; uint64_t v___x_4316_; 
v___x_4314_ = ((size_t)0ULL);
v___x_4315_ = lean_usize_of_nat(v___x_4308_);
v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4303_, v___x_4314_, v___x_4315_, v___x_4306_);
v___y_4297_ = v___y_4305_;
v___y_4298_ = v___x_4316_;
goto v___jp_4296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_4320_, lean_object* v_x_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4320_, v_x_4321_);
lean_dec_ref(v_x_4321_);
lean_dec_ref(v_x_4320_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* v_x_4323_, lean_object* v_x_4324_){
_start:
{
uint8_t v_stage_u2081_4325_; 
v_stage_u2081_4325_ = lean_ctor_get_uint8(v_x_4323_, sizeof(void*)*2);
if (v_stage_u2081_4325_ == 0)
{
lean_object* v_map_u2081_4326_; lean_object* v_map_u2082_4327_; lean_object* v___x_4328_; 
v_map_u2081_4326_ = lean_ctor_get(v_x_4323_, 0);
v_map_u2082_4327_ = lean_ctor_get(v_x_4323_, 1);
v___x_4328_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_4327_, v_x_4324_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4326_, v_x_4324_);
return v___x_4329_;
}
else
{
return v___x_4328_;
}
}
else
{
lean_object* v_map_u2081_4330_; lean_object* v___x_4331_; 
v_map_u2081_4330_ = lean_ctor_get(v_x_4323_, 0);
v___x_4331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4330_, v_x_4324_);
return v___x_4331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object* v_x_4332_, lean_object* v_x_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4332_, v_x_4333_);
lean_dec_ref(v_x_4333_);
lean_dec_ref(v_x_4332_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* v_as_4337_, size_t v_sz_4338_, size_t v_i_4339_, lean_object* v_b_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
uint8_t v___x_4346_; 
v___x_4346_ = lean_usize_dec_lt(v_i_4339_, v_sz_4338_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v_b_4340_);
return v___x_4347_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4349_; 
v_a_4348_ = lean_array_uget_borrowed(v_as_4337_, v_i_4339_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
lean_inc(v___y_4342_);
lean_inc_ref(v___y_4341_);
lean_inc(v_a_4348_);
v___x_4349_ = lean_infer_type(v_a_4348_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_4350_, v___y_4342_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4380_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4380_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4380_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v_snd_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4378_; 
v_snd_4356_ = lean_ctor_get(v_b_4340_, 1);
v_isSharedCheck_4378_ = !lean_is_exclusive(v_b_4340_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v_b_4340_, 0);
lean_dec(v_unused_4379_);
v___x_4358_ = v_b_4340_;
v_isShared_4359_ = v_isSharedCheck_4378_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_snd_4356_);
lean_dec(v_b_4340_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4378_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = l_Lean_Expr_headBeta(v_a_4352_);
v___x_4361_ = l_Lean_Expr_getAppFn(v___x_4360_);
lean_dec_ref(v___x_4360_);
if (lean_obj_tag(v___x_4361_) == 4)
{
lean_object* v_declName_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4366_; 
lean_del_object(v___x_4354_);
v_declName_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_declName_4362_);
lean_dec_ref_known(v___x_4361_, 2);
v___x_4363_ = lean_box(0);
v___x_4364_ = lean_array_push(v_snd_4356_, v_declName_4362_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v___x_4364_);
lean_ctor_set(v___x_4358_, 0, v___x_4363_);
v___x_4366_ = v___x_4358_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
size_t v___x_4367_; size_t v___x_4368_; 
v___x_4367_ = ((size_t)1ULL);
v___x_4368_ = lean_usize_add(v_i_4339_, v___x_4367_);
v_i_4339_ = v___x_4368_;
v_b_4340_ = v___x_4366_;
goto _start;
}
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
lean_dec_ref(v___x_4361_);
v___x_4371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0));
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4371_);
v___x_4373_ = v___x_4358_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4377_, 1, v_snd_4356_);
v___x_4373_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4375_; 
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4373_);
v___x_4375_ = v___x_4354_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v_b_4340_);
v_a_4381_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4351_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4351_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v_b_4340_);
v_a_4389_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4349_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4349_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* v_as_4397_, lean_object* v_sz_4398_, lean_object* v_i_4399_, lean_object* v_b_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
size_t v_sz_boxed_4406_; size_t v_i_boxed_4407_; lean_object* v_res_4408_; 
v_sz_boxed_4406_ = lean_unbox_usize(v_sz_4398_);
lean_dec(v_sz_4398_);
v_i_boxed_4407_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_res_4408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_4397_, v_sz_boxed_4406_, v_i_boxed_4407_, v_b_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec_ref(v_as_4397_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* v_targets_4412_, uint8_t v_induction_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v___x_4419_; size_t v_sz_4420_; size_t v___x_4421_; lean_object* v___x_4422_; 
v___x_4419_ = ((lean_object*)(l_Lean_Meta_getCustomEliminator_x3f___closed__0));
v_sz_4420_ = lean_array_size(v_targets_4412_);
v___x_4421_ = ((size_t)0ULL);
v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_4412_, v_sz_4420_, v___x_4421_, v___x_4419_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4454_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4454_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4454_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v_fst_4427_; 
v_fst_4427_ = lean_ctor_get(v_a_4423_, 0);
if (lean_obj_tag(v_fst_4427_) == 0)
{
lean_object* v_snd_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4448_; 
v_snd_4428_ = lean_ctor_get(v_a_4423_, 1);
v_isSharedCheck_4448_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; 
v_unused_4449_ = lean_ctor_get(v_a_4423_, 0);
lean_dec(v_unused_4449_);
v___x_4430_ = v_a_4423_;
v_isShared_4431_ = v_isSharedCheck_4448_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snd_4428_);
lean_dec(v_a_4423_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4448_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v_env_4433_; lean_object* v___x_4434_; lean_object* v_ext_4435_; lean_object* v_toEnvExtension_4436_; lean_object* v_asyncMode_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4432_ = lean_st_ref_get(v_a_4417_);
v_env_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc_ref(v_env_4433_);
lean_dec(v___x_4432_);
v___x_4434_ = l_Lean_Meta_customEliminatorExt;
v_ext_4435_ = lean_ctor_get(v___x_4434_, 1);
v_toEnvExtension_4436_ = lean_ctor_get(v_ext_4435_, 0);
v_asyncMode_4437_ = lean_ctor_get(v_toEnvExtension_4436_, 2);
v___x_4438_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4439_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4438_, v___x_4434_, v_env_4433_, v_asyncMode_4437_);
v___x_4440_ = lean_box(v_induction_4413_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4440_);
v___x_4442_ = v___x_4430_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4440_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_snd_4428_);
v___x_4442_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4443_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_4439_, v___x_4442_);
lean_dec_ref(v___x_4442_);
lean_dec(v___x_4439_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4443_);
v___x_4445_ = v___x_4425_;
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
}
else
{
lean_object* v_val_4450_; lean_object* v___x_4452_; 
lean_inc_ref(v_fst_4427_);
lean_dec(v_a_4423_);
v_val_4450_ = lean_ctor_get(v_fst_4427_, 0);
lean_inc(v_val_4450_);
lean_dec_ref_known(v_fst_4427_, 1);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v_val_4450_);
v___x_4452_ = v___x_4425_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_val_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
v_a_4455_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4422_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4422_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* v_targets_4463_, lean_object* v_induction_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
uint8_t v_induction_boxed_4470_; lean_object* v_res_4471_; 
v_induction_boxed_4470_ = lean_unbox(v_induction_4464_);
v_res_4471_ = l_Lean_Meta_getCustomEliminator_x3f(v_targets_4463_, v_induction_boxed_4470_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec_ref(v_targets_4463_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* v_00_u03b2_4472_, lean_object* v_x_4473_, lean_object* v_x_4474_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4473_, v_x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object* v_00_u03b2_4476_, lean_object* v_x_4477_, lean_object* v_x_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(v_00_u03b2_4476_, v_x_4477_, v_x_4478_);
lean_dec_ref(v_x_4478_);
lean_dec_ref(v_x_4477_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4480_, lean_object* v_x_4481_, lean_object* v_x_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4481_, v_x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4484_, lean_object* v_x_4485_, lean_object* v_x_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_4484_, v_x_4485_, v_x_4486_);
lean_dec_ref(v_x_4486_);
lean_dec_ref(v_x_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object* v_00_u03b2_4488_, lean_object* v_m_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4489_, v_a_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4492_, lean_object* v_m_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_4492_, v_m_4493_, v_a_4494_);
lean_dec_ref(v_a_4494_);
lean_dec_ref(v_m_4493_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4496_, lean_object* v_x_4497_, size_t v_x_4498_, lean_object* v_x_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4497_, v_x_4498_, v_x_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4501_, lean_object* v_x_4502_, lean_object* v_x_4503_, lean_object* v_x_4504_){
_start:
{
size_t v_x_2641__boxed_4505_; lean_object* v_res_4506_; 
v_x_2641__boxed_4505_ = lean_unbox_usize(v_x_4503_);
lean_dec(v_x_4503_);
v_res_4506_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_4501_, v_x_4502_, v_x_2641__boxed_4505_, v_x_4504_);
lean_dec_ref(v_x_4504_);
lean_dec_ref(v_x_4502_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4507_, lean_object* v_a_4508_, lean_object* v_x_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4508_, v_x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4511_, lean_object* v_a_4512_, lean_object* v_x_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_4511_, v_a_4512_, v_x_4513_);
lean_dec(v_x_4513_);
lean_dec_ref(v_a_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4515_, lean_object* v_keys_4516_, lean_object* v_vals_4517_, lean_object* v_heq_4518_, lean_object* v_i_4519_, lean_object* v_k_4520_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4516_, v_vals_4517_, v_i_4519_, v_k_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4522_, lean_object* v_keys_4523_, lean_object* v_vals_4524_, lean_object* v_heq_4525_, lean_object* v_i_4526_, lean_object* v_k_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_4522_, v_keys_4523_, v_vals_4524_, v_heq_4525_, v_i_4526_, v_k_4527_);
lean_dec_ref(v_k_4527_);
lean_dec_ref(v_vals_4524_);
lean_dec_ref(v_keys_4523_);
return v_res_4528_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedElimInfo_default = _init_l_Lean_Meta_instInhabitedElimInfo_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo_default);
l_Lean_Meta_instInhabitedElimInfo = _init_l_Lean_Meta_instInhabitedElimInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo);
l_Lean_Meta_instInhabitedCustomEliminators_default = _init_l_Lean_Meta_instInhabitedCustomEliminators_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators_default);
l_Lean_Meta_instInhabitedCustomEliminators = _init_l_Lean_Meta_instInhabitedCustomEliminators();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_customEliminatorExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_customEliminatorExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_ElimInfo(builtin);
}
#ifdef __cplusplus
}
#endif

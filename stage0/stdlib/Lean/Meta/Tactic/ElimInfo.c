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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_fget_borrowed(v_xs_711_, v_a_716_);
v___x_730_ = lean_expr_eqv(v___x_729_, v_motive_712_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Array_contains___at___00Lean_Meta_getElimExprInfo_spec__4(v___x_713_, v___x_729_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_Expr_fvarId_x21(v___x_729_);
v___x_733_ = l_Lean_FVarId_getDecl___redArg(v___x_732_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; uint8_t v___x_736_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_LocalDecl_binderInfo(v_a_734_);
v___x_736_ = l_Lean_BinderInfo_isExplicit(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_a_734_);
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_742_; lean_object* v___y_744_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = l_Lean_LocalDecl_type(v_a_734_);
v___x_739_ = l_Lean_Meta_altArity(v_motive_712_, v___x_737_, v___x_738_);
lean_dec_ref(v___x_738_);
v_fst_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_fst_740_);
v_snd_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_snd_741_);
lean_dec_ref(v___x_739_);
v___x_742_ = l_Lean_LocalDecl_userName(v_a_734_);
lean_dec(v_a_734_);
if (lean_obj_tag(v_baseDeclName_x3f_714_) == 0)
{
v___y_744_ = v_baseDeclName_x3f_714_;
goto v___jp_743_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_val_748_ = lean_ctor_get(v_baseDeclName_x3f_714_, 0);
lean_inc(v___x_742_);
lean_inc(v_val_748_);
v___x_749_ = l_Lean_Name_append(v_val_748_, v___x_742_);
lean_inc(v___x_749_);
lean_inc_ref(v___x_715_);
v___x_750_ = l_Lean_Environment_contains(v___x_715_, v___x_749_, v___x_736_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v___x_749_);
v___x_751_ = lean_box(0);
v___y_744_ = v___x_751_;
goto v___jp_743_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_749_);
v___y_744_ = v___x_752_;
goto v___jp_743_;
}
}
v___jp_743_:
{
lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___y_744_);
lean_ctor_set(v___x_745_, 2, v_fst_740_);
v___x_746_ = lean_unbox(v_snd_741_);
lean_dec(v_snd_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*3, v___x_746_);
v___x_747_ = lean_array_push(v_b_717_, v___x_745_);
v_a_723_ = v___x_747_;
goto v___jp_722_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_b_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v_baseDeclName_x3f_714_);
v_a_753_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_733_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_733_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
}
}
else
{
v_a_723_ = v_b_717_;
goto v___jp_722_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg___boxed(lean_object* v_upperBound_761_, lean_object* v_xs_762_, lean_object* v_motive_763_, lean_object* v___x_764_, lean_object* v_baseDeclName_x3f_765_, lean_object* v___x_766_, lean_object* v_a_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_761_, v_xs_762_, v_motive_763_, v___x_764_, v_baseDeclName_x3f_765_, v___x_766_, v_a_767_, v_b_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec_ref(v___x_764_);
lean_dec_ref(v_motive_763_);
lean_dec_ref(v_xs_762_);
lean_dec(v_upperBound_761_);
return v_res_773_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__2));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(lean_object* v_xs_780_, lean_object* v_a_781_, lean_object* v_elimExpr_782_, lean_object* v_baseDeclName_x3f_783_, lean_object* v_type_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; 
if (lean_obj_tag(v_x_785_) == 5)
{
lean_object* v_fn_868_; lean_object* v_arg_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_fn_868_ = lean_ctor_get(v_x_785_, 0);
lean_inc_ref(v_fn_868_);
v_arg_869_ = lean_ctor_get(v_x_785_, 1);
lean_inc_ref(v_arg_869_);
lean_dec_ref_known(v_x_785_, 2);
v___x_870_ = lean_array_set(v_x_786_, v_x_787_, v_arg_869_);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_sub(v_x_787_, v___x_871_);
lean_dec(v_x_787_);
v_x_785_ = v_fn_868_;
v_x_786_ = v___x_870_;
v_x_787_ = v___x_872_;
goto _start;
}
else
{
lean_object* v___f_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___x_887_; 
lean_dec(v_x_787_);
v___f_874_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__1));
v___x_887_ = l_Lean_Expr_isFVar(v_x_785_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v___x_888_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__3);
v___x_889_ = l_Lean_indentExpr(v_type_784_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_890_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_dec_ref(v_type_784_);
v___y_876_ = v___y_788_;
v___y_877_ = v___y_789_;
v___y_878_ = v___y_790_;
v___y_879_ = v___y_791_;
goto v___jp_875_;
}
v___jp_875_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_880_ = l_Array_takeWhile___redArg(v___f_874_, v_x_786_);
v___x_881_ = lean_array_get_size(v___x_880_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_array_get_size(v_x_786_);
v___x_884_ = lean_nat_dec_le(v___x_881_, v___x_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_881_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
v___y_794_ = v___y_876_;
v___y_795_ = v___y_879_;
v___y_796_ = v___y_878_;
v___y_797_ = v___y_877_;
v___y_798_ = v___x_880_;
v___y_799_ = v___x_885_;
goto v___jp_793_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_882_);
lean_ctor_set(v___x_886_, 1, v___x_883_);
v___y_794_ = v___y_876_;
v___y_795_ = v___y_879_;
v___y_796_ = v___y_878_;
v___y_797_ = v___y_877_;
v___y_798_ = v___x_880_;
v___y_799_ = v___x_886_;
goto v___jp_793_;
}
}
}
v___jp_793_:
{
lean_object* v___x_800_; 
lean_inc(v___y_795_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_794_);
lean_inc_ref(v_x_785_);
v___x_800_ = lean_infer_type(v_x_785_, v___y_794_, v___y_797_, v___y_796_, v___y_795_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___f_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc_n(v_a_801_, 2);
lean_dec_ref_known(v___x_800_, 1);
lean_inc_ref(v_x_786_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___lam__0___boxed), 9, 2);
lean_closure_set(v___f_802_, 0, v_a_801_);
lean_closure_set(v___f_802_, 1, v_x_786_);
v___x_803_ = 0;
v___x_804_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_801_, v___f_802_, v___x_803_, v___x_803_, v___y_794_, v___y_797_, v___y_796_, v___y_795_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_805_ = l_Array_idxOf_x3f___at___00Lean_Meta_getElimExprInfo_spec__0(v_xs_780_, v_x_785_);
if (lean_obj_tag(v___x_805_) == 1)
{
lean_object* v_val_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_805_, 1);
v_sz_807_ = lean_array_size(v___y_798_);
v___x_808_ = ((size_t)0ULL);
lean_inc_ref(v___y_798_);
lean_inc_ref(v_a_781_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3(v_xs_780_, v_a_781_, v_sz_807_, v___x_808_, v___y_798_, v___y_794_, v___y_797_, v___y_796_, v___y_795_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v_lower_812_; lean_object* v_upper_813_; lean_object* v_env_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_st_ref_get(v___y_795_);
v_lower_812_ = lean_ctor_get(v___y_799_, 0);
lean_inc(v_lower_812_);
v_upper_813_ = lean_ctor_get(v___y_799_, 1);
lean_inc(v_upper_813_);
lean_dec_ref(v___y_799_);
v_env_814_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_env_814_);
lean_dec(v___x_811_);
v___x_815_ = lean_array_get_size(v_xs_780_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___closed__0));
v___x_818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v___x_815_, v_xs_780_, v_x_785_, v___y_798_, v_baseDeclName_x3f_783_, v_env_814_, v___x_816_, v___x_817_, v___y_794_, v___y_796_, v___y_795_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_785_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_831_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v_start_824_; lean_object* v_stop_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_823_ = l_Array_toSubarray___redArg(v_x_786_, v_lower_812_, v_upper_813_);
v_start_824_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_start_824_);
v_stop_825_ = lean_ctor_get(v___x_823_, 2);
lean_inc(v_stop_825_);
lean_dec_ref(v___x_823_);
v___x_826_ = lean_nat_sub(v_stop_825_, v_start_824_);
lean_dec(v_start_824_);
lean_dec(v_stop_825_);
v___x_827_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_827_, 0, v_elimExpr_782_);
lean_ctor_set(v___x_827_, 1, v_a_781_);
lean_ctor_set(v___x_827_, 2, v_val_806_);
lean_ctor_set(v___x_827_, 3, v_a_810_);
lean_ctor_set(v___x_827_, 4, v_a_819_);
lean_ctor_set(v___x_827_, 5, v___x_826_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_upper_813_);
lean_dec(v_lower_812_);
lean_dec(v_a_810_);
lean_dec(v_val_806_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_832_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_val_806_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_840_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_809_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_809_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v___x_805_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
v___x_848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getElimExprInfo_spec__3___closed__1);
v___x_849_ = l_Lean_indentExpr(v_a_781_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_850_, v___y_794_, v___y_797_, v___y_796_, v___y_795_);
return v___x_851_;
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_852_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_804_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_804_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_baseDeclName_x3f_783_);
lean_dec_ref(v_elimExpr_782_);
lean_dec_ref(v_a_781_);
v_a_860_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_800_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_800_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6___boxed(lean_object* v_xs_900_, lean_object* v_a_901_, lean_object* v_elimExpr_902_, lean_object* v_baseDeclName_x3f_903_, lean_object* v_type_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_900_, v_a_901_, v_elimExpr_902_, v_baseDeclName_x3f_903_, v_type_904_, v_x_905_, v_x_906_, v_x_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_xs_900_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0(void){
_start:
{
lean_object* v___x_914_; lean_object* v_dummy_915_; 
v___x_914_ = lean_box(0);
v_dummy_915_ = l_Lean_Expr_sort___override(v___x_914_);
return v_dummy_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* v_a_916_, lean_object* v_elimExpr_917_, lean_object* v_baseDeclName_x3f_918_, lean_object* v_xs_919_, lean_object* v_type_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_dummy_926_; lean_object* v_nargs_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_dummy_926_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___lam__0___closed__0, &l_Lean_Meta_getElimExprInfo___lam__0___closed__0_once, _init_l_Lean_Meta_getElimExprInfo___lam__0___closed__0);
v_nargs_927_ = l_Lean_Expr_getAppNumArgs(v_type_920_);
lean_inc(v_nargs_927_);
v___x_928_ = lean_mk_array(v_nargs_927_, v_dummy_926_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v_nargs_927_, v___x_929_);
lean_dec(v_nargs_927_);
lean_inc_ref(v_type_920_);
v___x_931_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getElimExprInfo_spec__6(v_xs_919_, v_a_916_, v_elimExpr_917_, v_baseDeclName_x3f_918_, v_type_920_, v_type_920_, v___x_928_, v___x_930_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* v_a_932_, lean_object* v_elimExpr_933_, lean_object* v_baseDeclName_x3f_934_, lean_object* v_xs_935_, lean_object* v_type_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_getElimExprInfo___lam__0(v_a_932_, v_elimExpr_933_, v_baseDeclName_x3f_934_, v_xs_935_, v_type_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_xs_935_);
return v_res_942_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_943_; double v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_float_of_nat(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(lean_object* v_cls_948_, lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_ref_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1001_; 
v_ref_955_ = lean_ctor_get(v___y_952_, 5);
v___x_956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1_spec__2(v_msg_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_1001_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1001_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v_traceState_962_; lean_object* v_env_963_; lean_object* v_nextMacroScope_964_; lean_object* v_ngen_965_; lean_object* v_auxDeclNGen_966_; lean_object* v_cache_967_; lean_object* v_messages_968_; lean_object* v_infoState_969_; lean_object* v_snapshotTasks_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v___x_961_ = lean_st_ref_take(v___y_953_);
v_traceState_962_ = lean_ctor_get(v___x_961_, 4);
v_env_963_ = lean_ctor_get(v___x_961_, 0);
v_nextMacroScope_964_ = lean_ctor_get(v___x_961_, 1);
v_ngen_965_ = lean_ctor_get(v___x_961_, 2);
v_auxDeclNGen_966_ = lean_ctor_get(v___x_961_, 3);
v_cache_967_ = lean_ctor_get(v___x_961_, 5);
v_messages_968_ = lean_ctor_get(v___x_961_, 6);
v_infoState_969_ = lean_ctor_get(v___x_961_, 7);
v_snapshotTasks_970_ = lean_ctor_get(v___x_961_, 8);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_972_ = v___x_961_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snapshotTasks_970_);
lean_inc(v_infoState_969_);
lean_inc(v_messages_968_);
lean_inc(v_cache_967_);
lean_inc(v_traceState_962_);
lean_inc(v_auxDeclNGen_966_);
lean_inc(v_ngen_965_);
lean_inc(v_nextMacroScope_964_);
lean_inc(v_env_963_);
lean_dec(v___x_961_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint64_t v_tid_974_; lean_object* v_traces_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_999_; 
v_tid_974_ = lean_ctor_get_uint64(v_traceState_962_, sizeof(void*)*1);
v_traces_975_ = lean_ctor_get(v_traceState_962_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_traceState_962_);
if (v_isSharedCheck_999_ == 0)
{
v___x_977_ = v_traceState_962_;
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_traces_975_);
lean_dec(v_traceState_962_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; double v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_979_ = lean_box(0);
v___x_980_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0, &l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__0);
v___x_981_ = 0;
v___x_982_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__1));
v___x_983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_983_, 0, v_cls_948_);
lean_ctor_set(v___x_983_, 1, v___x_979_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
lean_ctor_set_float(v___x_983_, sizeof(void*)*3, v___x_980_);
lean_ctor_set_float(v___x_983_, sizeof(void*)*3 + 8, v___x_980_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*3 + 16, v___x_981_);
v___x_984_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___closed__2));
v___x_985_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v_a_957_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
lean_inc(v_ref_955_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_ref_955_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_PersistentArray_push___redArg(v_traces_975_, v___x_986_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_987_);
v___x_989_ = v___x_977_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_987_);
lean_ctor_set_uint64(v_reuseFailAlloc_998_, sizeof(void*)*1, v_tid_974_);
v___x_989_ = v_reuseFailAlloc_998_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 4, v___x_989_);
v___x_991_ = v___x_972_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_env_963_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_964_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_965_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_966_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_cache_967_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_messages_968_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_infoState_969_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_snapshotTasks_970_);
v___x_991_ = v_reuseFailAlloc_997_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_st_ref_set(v___y_953_, v___x_991_);
v___x_993_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_993_);
v___x_995_ = v___x_959_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7___boxed(lean_object* v_cls_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v_cls_1002_, v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__5(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1019_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__4));
v___x_1020_ = l_Lean_Name_append(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__7(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__6));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Meta_getElimExprInfo___closed__9(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__8));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* v_elimExpr_1027_, lean_object* v_baseDeclName_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
lean_inc(v_a_1032_);
lean_inc_ref(v_a_1031_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
lean_inc_ref(v_elimExpr_1027_);
v___x_1034_ = lean_infer_type(v_elimExpr_1027_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_options_1035_; lean_object* v_a_1036_; lean_object* v_inheritedTraceOptions_1037_; uint8_t v_hasTrace_1038_; lean_object* v___f_1039_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; 
v_options_1035_ = lean_ctor_get(v_a_1031_, 2);
v_a_1036_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_n(v_a_1036_, 2);
lean_dec_ref_known(v___x_1034_, 1);
v_inheritedTraceOptions_1037_ = lean_ctor_get(v_a_1031_, 13);
v_hasTrace_1038_ = lean_ctor_get_uint8(v_options_1035_, sizeof(void*)*1);
lean_inc_ref(v_elimExpr_1027_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1039_, 0, v_a_1036_);
lean_closure_set(v___f_1039_, 1, v_elimExpr_1027_);
lean_closure_set(v___f_1039_, 2, v_baseDeclName_x3f_1028_);
if (v_hasTrace_1038_ == 0)
{
lean_dec_ref(v_elimExpr_1027_);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_getElimExprInfo___closed__2));
v___x_1048_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__5, &l_Lean_Meta_getElimExprInfo___closed__5_once, _init_l_Lean_Meta_getElimExprInfo___closed__5);
v___x_1049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1037_, v_options_1035_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v_elimExpr_1027_);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1050_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__7, &l_Lean_Meta_getElimExprInfo___closed__7_once, _init_l_Lean_Meta_getElimExprInfo___closed__7);
v___x_1051_ = l_Lean_indentExpr(v_elimExpr_1027_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_Meta_getElimExprInfo___closed__9, &l_Lean_Meta_getElimExprInfo___closed__9_once, _init_l_Lean_Meta_getElimExprInfo___closed__9);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_inc(v_a_1036_);
v___x_1055_ = l_Lean_indentExpr(v_a_1036_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_addTrace___at___00Lean_Meta_getElimExprInfo_spec__7(v___x_1047_, v___x_1056_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
v___y_1041_ = v_a_1029_;
v___y_1042_ = v_a_1030_;
v___y_1043_ = v_a_1031_;
v___y_1044_ = v_a_1032_;
goto v___jp_1040_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___f_1039_);
lean_dec(v_a_1036_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
v___jp_1040_:
{
uint8_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = 0;
v___x_1046_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v_a_1036_, v___f_1039_, v___x_1045_, v___x_1045_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_baseDeclName_x3f_1028_);
lean_dec_ref(v_elimExpr_1027_);
v_a_1066_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1034_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1034_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___boxed(lean_object* v_elimExpr_1074_, lean_object* v_baseDeclName_x3f_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_getElimExprInfo(v_elimExpr_1074_, v_baseDeclName_x3f_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(lean_object* v_00_u03b1_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1(v_00_u03b1_1090_, v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(lean_object* v_upperBound_1098_, lean_object* v_xs_1099_, lean_object* v_motive_1100_, lean_object* v___x_1101_, lean_object* v_baseDeclName_x3f_1102_, lean_object* v___x_1103_, lean_object* v_inst_1104_, lean_object* v_R_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_, lean_object* v_c_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___redArg(v_upperBound_1098_, v_xs_1099_, v_motive_1100_, v___x_1101_, v_baseDeclName_x3f_1102_, v___x_1103_, v_a_1106_, v_b_1107_, v___y_1109_, v___y_1111_, v___y_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* v_upperBound_1115_, lean_object* v_xs_1116_, lean_object* v_motive_1117_, lean_object* v___x_1118_, lean_object* v_baseDeclName_x3f_1119_, lean_object* v___x_1120_, lean_object* v_inst_1121_, lean_object* v_R_1122_, lean_object* v_a_1123_, lean_object* v_b_1124_, lean_object* v_c_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getElimExprInfo_spec__5(v_upperBound_1115_, v_xs_1116_, v_motive_1117_, v___x_1118_, v_baseDeclName_x3f_1119_, v___x_1120_, v_inst_1121_, v_R_1122_, v_a_1123_, v_b_1124_, v_c_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_motive_1117_);
lean_dec_ref(v_xs_1116_);
lean_dec(v_upperBound_1115_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* v_elimName_1132_, lean_object* v_baseDeclName_x3f_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_elimName_1132_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = l_Lean_Meta_getElimExprInfo(v_a_1140_, v_baseDeclName_x3f_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_baseDeclName_x3f_1133_);
v_a_1142_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1139_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___boxed(lean_object* v_elimName_1150_, lean_object* v_baseDeclName_x3f_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_getElimInfo(v_elimName_1150_, v_baseDeclName_x3f_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* v_a_1158_, lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_eq(v_i_1160_, v_stop_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_array_uget_borrowed(v_as_1159_, v_i_1160_);
v___x_1164_ = lean_nat_dec_eq(v_a_1158_, v___x_1163_);
if (v___x_1164_ == 0)
{
size_t v___x_1165_; size_t v___x_1166_; 
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_add(v_i_1160_, v___x_1165_);
v_i_1160_ = v___x_1166_;
goto _start;
}
else
{
return v___x_1164_;
}
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = 0;
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* v_a_1169_, lean_object* v_as_1170_, lean_object* v_i_1171_, lean_object* v_stop_1172_){
_start:
{
size_t v_i_boxed_1173_; size_t v_stop_boxed_1174_; uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_i_boxed_1173_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_stop_boxed_1174_ = lean_unbox_usize(v_stop_1172_);
lean_dec(v_stop_1172_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1169_, v_as_1170_, v_i_boxed_1173_, v_stop_boxed_1174_);
lean_dec_ref(v_as_1170_);
lean_dec(v_a_1169_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* v_as_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_array_get_size(v_as_1177_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1180_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(v_a_1178_, v_as_1177_, v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* v_as_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_as_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_as_1185_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__1));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__3));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__5));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__7));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__9));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(lean_object* v_elimInfo_1206_, lean_object* v_targets_1207_, lean_object* v_type_1208_, lean_object* v_argIdx_1209_, lean_object* v_targetIdx_1210_, lean_object* v_implicits_1211_, lean_object* v_targets_x27_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_whnfD(v_type_1208_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
if (lean_obj_tag(v_a_1222_) == 7)
{
lean_object* v_binderName_1223_; lean_object* v_binderType_1224_; lean_object* v_body_1225_; uint8_t v_binderInfo_1226_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v_elimExpr_1294_; lean_object* v_targetsPos_1295_; uint8_t v___x_1296_; 
v_binderName_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_binderName_1223_);
v_binderType_1224_ = lean_ctor_get(v_a_1222_, 1);
lean_inc_ref(v_binderType_1224_);
v_body_1225_ = lean_ctor_get(v_a_1222_, 2);
lean_inc_ref(v_body_1225_);
v_binderInfo_1226_ = lean_ctor_get_uint8(v_a_1222_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1222_, 3);
v_elimExpr_1294_ = lean_ctor_get(v_elimInfo_1206_, 0);
v_targetsPos_1295_ = lean_ctor_get(v_elimInfo_1206_, 3);
v___x_1296_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect_spec__0(v_targetsPos_1295_, v_argIdx_1209_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_binderName_1223_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_binderType_1224_);
v___x_1298_ = 0;
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Lean_Meta_mkFreshExprMVar(v___x_1297_, v___x_1298_, v___x_1299_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = lean_expr_instantiate1(v_body_1225_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_body_1225_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_nat_add(v_argIdx_1209_, v___x_1303_);
lean_dec(v_argIdx_1209_);
v_type_1208_ = v___x_1302_;
v_argIdx_1209_ = v___x_1304_;
goto _start;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1306_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1300_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1300_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_1226_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_binderType_1224_);
v___x_1316_ = 0;
v___x_1317_ = l_Lean_Meta_mkFreshExprMVar(v___x_1315_, v___x_1316_, v_binderName_1223_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_expr_instantiate1(v_body_1225_, v_a_1318_);
lean_dec_ref(v_body_1225_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_argIdx_1209_, v___x_1320_);
lean_dec(v_argIdx_1209_);
v___x_1322_ = l_Lean_Expr_mvarId_x21(v_a_1318_);
v___x_1323_ = lean_array_push(v_implicits_1211_, v___x_1322_);
v___x_1324_ = lean_array_push(v_targets_x27_1212_, v_a_1318_);
v_type_1208_ = v___x_1319_;
v_argIdx_1209_ = v___x_1321_;
v_implicits_1211_ = v___x_1323_;
v_targets_x27_1212_ = v___x_1324_;
goto _start;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1326_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1317_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1317_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
lean_dec(v_binderName_1223_);
v___x_1334_ = lean_array_get_size(v_targets_1207_);
v___x_1335_ = lean_nat_dec_lt(v_targetIdx_1210_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__6);
lean_inc_ref(v_elimExpr_1294_);
v___x_1337_ = l_Lean_MessageData_ofExpr(v_elimExpr_1294_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1340_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v___y_1240_ = v_a_1213_;
v___y_1241_ = v_a_1214_;
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
v___y_1240_ = v_a_1213_;
v___y_1241_ = v_a_1214_;
v___y_1242_ = v_a_1215_;
v___y_1243_ = v_a_1216_;
goto v___jp_1239_;
}
}
}
v___jp_1227_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1233_ = lean_expr_instantiate1(v_body_1225_, v___y_1228_);
lean_dec_ref(v_body_1225_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_argIdx_1209_, v___x_1234_);
lean_dec(v_argIdx_1209_);
v___x_1236_ = lean_nat_add(v_targetIdx_1210_, v___x_1234_);
lean_dec(v_targetIdx_1210_);
v___x_1237_ = lean_array_push(v_targets_x27_1212_, v___y_1228_);
v_type_1208_ = v___x_1233_;
v_argIdx_1209_ = v___x_1235_;
v_targetIdx_1210_ = v___x_1236_;
v_targets_x27_1212_ = v___x_1237_;
v_a_1213_ = v___y_1229_;
v_a_1214_ = v___y_1230_;
v_a_1215_ = v___y_1231_;
v_a_1216_ = v___y_1232_;
goto _start;
}
v___jp_1239_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_Lean_instInhabitedExpr;
v___x_1245_ = lean_array_get_borrowed(v___x_1244_, v_targets_1207_, v_targetIdx_1210_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___x_1245_);
v___x_1246_ = lean_infer_type(v___x_1245_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc_n(v_a_1247_, 2);
lean_dec_ref_known(v___x_1246_, 1);
lean_inc_ref(v_binderType_1224_);
v___x_1248_ = l_Lean_Meta_isExprDefEq(v_binderType_1224_, v_a_1247_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; uint8_t v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__0));
v___x_1253_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_1247_, v_binderType_1224_, v___x_1251_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__2);
lean_inc(v___x_1245_);
v___x_1256_ = l_Lean_indentExpr(v___x_1245_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__4);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1254_);
v___x_1261_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1260_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_dec_ref_known(v___x_1261_, 1);
lean_inc(v___x_1245_);
v___y_1228_ = v___x_1245_;
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
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
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1270_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1253_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1253_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
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
lean_dec(v_a_1247_);
lean_dec_ref(v_binderType_1224_);
lean_inc(v___x_1245_);
v___y_1228_ = v___x_1245_;
v___y_1229_ = v___y_1240_;
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
goto v___jp_1227_;
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1247_);
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1278_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1248_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1248_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
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
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_body_1225_);
lean_dec_ref(v_binderType_1224_);
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1286_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1246_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1246_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_dec(v_a_1222_);
lean_dec(v_argIdx_1209_);
v___x_1350_ = lean_array_get_size(v_targets_1207_);
v___x_1351_ = lean_nat_dec_eq(v_targetIdx_1210_, v___x_1350_);
lean_dec(v_targetIdx_1210_);
if (v___x_1351_ == 0)
{
lean_object* v_elimExpr_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_elimExpr_1352_ = lean_ctor_get(v_elimInfo_1206_, 0);
lean_inc_ref(v_elimExpr_1352_);
lean_dec_ref(v_elimInfo_1206_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__10);
v___x_1354_ = l_Lean_MessageData_ofExpr(v_elimExpr_1352_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1357_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
goto v___jp_1218_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_dec_ref(v_elimInfo_1206_);
goto v___jp_1218_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_targets_x27_1212_);
lean_dec_ref(v_implicits_1211_);
lean_dec(v_targetIdx_1210_);
lean_dec(v_argIdx_1209_);
lean_dec_ref(v_elimInfo_1206_);
v_a_1367_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1221_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1221_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_implicits_1211_);
lean_ctor_set(v___x_1219_, 1, v_targets_x27_1212_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___boxed(lean_object* v_elimInfo_1375_, lean_object* v_targets_1376_, lean_object* v_type_1377_, lean_object* v_argIdx_1378_, lean_object* v_targetIdx_1379_, lean_object* v_implicits_1380_, lean_object* v_targets_x27_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1375_, v_targets_1376_, v_type_1377_, v_argIdx_1378_, v_targetIdx_1379_, v_implicits_1380_, v_targets_x27_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec_ref(v_targets_1376_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(lean_object* v_e_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = l_Lean_Expr_hasMVar(v_e_1388_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_e_1388_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v_mctx_1394_; lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v_cache_1399_; lean_object* v_zetaDeltaFVarIds_1400_; lean_object* v_postponed_1401_; lean_object* v_diag_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v___x_1393_ = lean_st_ref_get(v___y_1389_);
v_mctx_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_ref(v_mctx_1394_);
lean_dec(v___x_1393_);
v___x_1395_ = l_Lean_instantiateMVarsCore(v_mctx_1394_, v_e_1388_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_st_ref_take(v___y_1389_);
v_cache_1399_ = lean_ctor_get(v___x_1398_, 1);
v_zetaDeltaFVarIds_1400_ = lean_ctor_get(v___x_1398_, 2);
v_postponed_1401_ = lean_ctor_get(v___x_1398_, 3);
v_diag_1402_ = lean_ctor_get(v___x_1398_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1412_);
v___x_1404_ = v___x_1398_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_diag_1402_);
lean_inc(v_postponed_1401_);
lean_inc(v_zetaDeltaFVarIds_1400_);
lean_inc(v_cache_1399_);
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_snd_1397_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_snd_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_zetaDeltaFVarIds_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_postponed_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_diag_1402_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_st_ref_set(v___y_1389_, v___x_1407_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_fst_1396_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg___boxed(lean_object* v_e_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1413_, v___y_1414_);
lean_dec(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(lean_object* v_e_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_e_1417_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___boxed(lean_object* v_e_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2(v_e_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1431_, lean_object* v_i_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_array_get_size(v_keys_1431_);
v___x_1435_ = lean_nat_dec_lt(v_i_1432_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec(v_i_1432_);
return v___x_1435_;
}
else
{
lean_object* v_k_x27_1436_; uint8_t v___x_1437_; 
v_k_x27_1436_ = lean_array_fget_borrowed(v_keys_1431_, v_i_1432_);
v___x_1437_ = l_Lean_instBEqMVarId_beq(v_k_1433_, v_k_x27_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_i_1432_, v___x_1438_);
lean_dec(v_i_1432_);
v_i_1432_ = v___x_1439_;
goto _start;
}
else
{
lean_dec(v_i_1432_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1441_, lean_object* v_i_1442_, lean_object* v_k_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1441_, v_i_1442_, v_k_1443_);
lean_dec(v_k_1443_);
lean_dec_ref(v_keys_1441_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1446_, size_t v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
lean_object* v_es_1449_; lean_object* v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; lean_object* v_j_1453_; lean_object* v___x_1454_; 
v_es_1449_ = lean_ctor_get(v_x_1446_, 0);
v___x_1450_ = lean_box(2);
v___x_1451_ = ((size_t)31ULL);
v___x_1452_ = lean_usize_land(v_x_1447_, v___x_1451_);
v_j_1453_ = lean_usize_to_nat(v___x_1452_);
v___x_1454_ = lean_array_get_borrowed(v___x_1450_, v_es_1449_, v_j_1453_);
lean_dec(v_j_1453_);
switch(lean_obj_tag(v___x_1454_))
{
case 0:
{
lean_object* v_key_1455_; uint8_t v___x_1456_; 
v_key_1455_ = lean_ctor_get(v___x_1454_, 0);
v___x_1456_ = l_Lean_instBEqMVarId_beq(v_x_1448_, v_key_1455_);
return v___x_1456_;
}
case 1:
{
lean_object* v_node_1457_; size_t v___x_1458_; size_t v___x_1459_; 
v_node_1457_ = lean_ctor_get(v___x_1454_, 0);
v___x_1458_ = ((size_t)5ULL);
v___x_1459_ = lean_usize_shift_right(v_x_1447_, v___x_1458_);
v_x_1446_ = v_node_1457_;
v_x_1447_ = v___x_1459_;
goto _start;
}
default: 
{
uint8_t v___x_1461_; 
v___x_1461_ = 0;
return v___x_1461_;
}
}
}
else
{
lean_object* v_ks_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_ks_1462_ = lean_ctor_get(v_x_1446_, 0);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1462_, v___x_1463_, v_x_1448_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
size_t v_x_3335__boxed_1468_; uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_x_3335__boxed_1468_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1469_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1465_, v_x_3335__boxed_1468_, v_x_1467_);
lean_dec(v_x_1467_);
lean_dec_ref(v_x_1465_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
uint64_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = l_Lean_instHashableMVarId_hash(v_x_1472_);
v___x_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1471_, v___x_1474_, v_x_1472_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1476_, v_x_1477_);
lean_dec(v_x_1477_);
lean_dec_ref(v_x_1476_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* v_mvarId_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v_mctx_1484_; lean_object* v_eAssignment_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = lean_st_ref_get(v___y_1481_);
v_mctx_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_mctx_1484_);
lean_dec(v___x_1483_);
v_eAssignment_1485_ = lean_ctor_get(v_mctx_1484_, 8);
lean_inc_ref(v_eAssignment_1485_);
lean_dec_ref(v_mctx_1484_);
v___x_1486_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_eAssignment_1485_, v_mvarId_1480_);
lean_dec_ref(v_eAssignment_1485_);
v___x_1487_ = lean_box(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* v_mvarId_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec(v_mvarId_1489_);
return v_res_1492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__0));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__2));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_a_1509_; uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_b_1502_);
return v___x_1514_;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
v___x_1516_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_a_1515_, v___y_1504_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_unbox(v_a_1517_);
lean_dec(v_a_1517_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_inc(v_a_1515_);
v___x_1520_ = l_Lean_MVarId_getDecl(v_a_1515_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_userName_1525_; uint8_t v___x_1526_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v_userName_1525_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_userName_1525_);
lean_dec(v_a_1521_);
v___x_1526_ = l_Lean_Name_isAnonymous(v_userName_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
v___x_1527_ = l_Lean_Name_hasMacroScopes(v_userName_1525_);
lean_dec(v_userName_1525_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_a_1515_);
v___x_1528_ = l_Lean_MVarId_getDecl(v_a_1515_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_userName_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_userName_1530_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_userName_1530_);
lean_dec(v_a_1529_);
v___x_1531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__3);
v___x_1532_ = l_Lean_MessageData_ofName(v_userName_1530_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1535_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_dec_ref_known(v___x_1536_, 1);
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
else
{
return v___x_1536_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1528_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
goto v___jp_1522_;
}
}
else
{
lean_dec(v_userName_1525_);
goto v___jp_1522_;
}
v___jp_1522_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___closed__1);
v___x_1524_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_1523_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref_known(v___x_1524_, 1);
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
else
{
return v___x_1524_;
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v_a_1545_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1520_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1520_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
v_a_1509_ = v___x_1518_;
goto v___jp_1508_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_a_1553_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1516_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1516_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
v___jp_1508_:
{
size_t v___x_1510_; size_t v___x_1511_; 
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1501_, v___x_1510_);
v_i_1501_ = v___x_1511_;
v_b_1502_ = v_a_1509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1___boxed(lean_object* v_as_1561_, lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_as_1561_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v_as_1561_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(size_t v_sz_1573_, size_t v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_usize_dec_lt(v_i_1574_, v_sz_1573_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_bs_1575_);
return v___x_1582_;
}
else
{
lean_object* v_v_1583_; lean_object* v___x_1584_; 
v_v_1583_ = lean_array_uget_borrowed(v_bs_1575_, v_i_1574_);
lean_inc(v_v_1583_);
v___x_1584_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_v_1583_, v___y_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v_bs_x27_1587_; size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_bs_x27_1587_ = lean_array_uset(v_bs_1575_, v_i_1574_, v___x_1586_);
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1574_, v___x_1588_);
v___x_1590_ = lean_array_uset(v_bs_x27_1587_, v_i_1574_, v_a_1585_);
v_i_1574_ = v___x_1589_;
v_bs_1575_ = v___x_1590_;
goto _start;
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_bs_1575_);
v_a_1592_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1584_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1584_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_boxed_1608_, v_i_boxed_1609_, v_bs_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* v_elimInfo_1613_, lean_object* v_targets_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_elimType_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_elimType_1620_ = lean_ctor_get(v_elimInfo_1613_, 1);
lean_inc_ref(v_elimType_1620_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_1623_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect(v_elimInfo_1613_, v_targets_1614_, v_elimType_1620_, v___x_1621_, v___x_1621_, v___x_1622_, v___x_1622_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; size_t v_sz_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_fst_1625_);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
lean_inc(v_snd_1626_);
lean_dec(v_a_1624_);
v___x_1627_ = lean_box(0);
v_sz_1628_ = lean_array_size(v_fst_1625_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_addImplicitTargets_spec__1(v_fst_1625_, v_sz_1628_, v___x_1629_, v___x_1627_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_fst_1625_);
if (lean_obj_tag(v___x_1630_) == 0)
{
size_t v_sz_1631_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1630_, 1);
v_sz_1631_ = lean_array_size(v_snd_1626_);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_addImplicitTargets_spec__3(v_sz_1631_, v___x_1629_, v_snd_1626_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
return v___x_1632_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_snd_1626_);
v_a_1633_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1630_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1630_);
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
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1623_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1623_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* v_elimInfo_1649_, lean_object* v_targets_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_addImplicitTargets(v_elimInfo_1649_, v_targets_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_targets_1650_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(lean_object* v_mvarId_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___redArg(v_mvarId_1657_, v___y_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* v_mvarId_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0(v_mvarId_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_mvarId_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* v_00_u03b2_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(v_x_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_res_1678_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0(v_00_u03b2_1675_, v_x_1676_, v_x_1677_);
lean_dec(v_x_1677_);
lean_dec_ref(v_x_1676_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, size_t v_x_1682_, lean_object* v_x_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___redArg(v_x_1681_, v_x_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
size_t v_x_3678__boxed_1689_; uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_x_3678__boxed_1689_ = lean_unbox_usize(v_x_1687_);
lean_dec(v_x_1687_);
v_res_1690_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2(v_00_u03b2_1685_, v_x_1686_, v_x_3678__boxed_1689_, v_x_1688_);
lean_dec(v_x_1688_);
lean_dec_ref(v_x_1686_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1692_, lean_object* v_keys_1693_, lean_object* v_vals_1694_, lean_object* v_heq_1695_, lean_object* v_i_1696_, lean_object* v_k_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1693_, v_i_1696_, v_k_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1699_, lean_object* v_keys_1700_, lean_object* v_vals_1701_, lean_object* v_heq_1702_, lean_object* v_i_1703_, lean_object* v_k_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1699_, v_keys_1700_, v_vals_1701_, v_heq_1702_, v_i_1703_, v_k_1704_);
lean_dec(v_k_1704_);
lean_dec_ref(v_vals_1701_);
lean_dec_ref(v_keys_1700_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_dec(v_x_1715_);
return v_x_1716_;
}
else
{
lean_object* v_head_1718_; lean_object* v_tail_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1730_; 
v_head_1718_ = lean_ctor_get(v_x_1717_, 0);
v_tail_1719_ = lean_ctor_get(v_x_1717_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1721_ = v_x_1717_;
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_tail_1719_);
lean_inc(v_head_1718_);
lean_dec(v_x_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
lean_inc(v_x_1715_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 5);
lean_ctor_set(v___x_1721_, 1, v_x_1715_);
lean_ctor_set(v___x_1721_, 0, v_x_1716_);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_x_1716_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_x_1715_);
v___x_1724_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = l_Lean_Name_reprPrec(v_head_1718_, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v_x_1716_ = v___x_1727_;
v_x_1717_ = v_tail_1719_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_dec(v_x_1731_);
return v_x_1732_;
}
else
{
lean_object* v_head_1734_; lean_object* v_tail_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1746_; 
v_head_1734_ = lean_ctor_get(v_x_1733_, 0);
v_tail_1735_ = lean_ctor_get(v_x_1733_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1733_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1737_ = v_x_1733_;
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_tail_1735_);
lean_inc(v_head_1734_);
lean_dec(v_x_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
lean_inc(v_x_1731_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 5);
lean_ctor_set(v___x_1737_, 1, v_x_1731_);
lean_ctor_set(v___x_1737_, 0, v_x_1732_);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_x_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_x_1731_);
v___x_1740_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = l_Lean_Name_reprPrec(v_head_1734_, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1_spec__2(v_x_1731_, v___x_1743_, v_tail_1735_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = l_Lean_Name_reprPrec(v___y_1747_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_x_1751_);
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v_tail_1753_; 
v_tail_1753_ = lean_ctor_get(v_x_1750_, 1);
if (lean_obj_tag(v_tail_1753_) == 0)
{
lean_object* v_head_1754_; lean_object* v___x_1755_; 
lean_dec(v_x_1751_);
v_head_1754_ = lean_ctor_get(v_x_1750_, 0);
lean_inc(v_head_1754_);
lean_dec_ref_known(v_x_1750_, 2);
v___x_1755_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1754_);
return v___x_1755_;
}
else
{
lean_object* v_head_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_inc(v_tail_1753_);
v_head_1756_ = lean_ctor_get(v_x_1750_, 0);
lean_inc(v_head_1756_);
lean_dec_ref_known(v_x_1750_, 2);
v___x_1757_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0___lam__0(v_head_1756_);
v___x_1758_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0_spec__1(v_x_1751_, v___x_1757_, v_tail_1753_);
return v___x_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(lean_object* v_xs_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = lean_array_get_size(v_xs_1759_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1763_ = lean_array_to_list(v_xs_1759_);
v___x_1764_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_1765_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0_spec__0(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__4);
v___x_1767_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__5));
v___x_1768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1765_);
v___x_1769_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_1770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1766_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = l_Std_Format_fill(v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; 
lean_dec_ref(v_xs_1759_);
v___x_1773_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__8));
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___redArg(lean_object* v_x_1788_){
_start:
{
uint8_t v_induction_1789_; lean_object* v_typeNames_1790_; lean_object* v_elimName_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_induction_1789_ = lean_ctor_get_uint8(v_x_1788_, sizeof(void*)*2);
v_typeNames_1790_ = lean_ctor_get(v_x_1788_, 0);
lean_inc_ref(v_typeNames_1790_);
v_elimName_1791_ = lean_ctor_get(v_x_1788_, 1);
lean_inc(v_elimName_1791_);
lean_dec_ref(v_x_1788_);
v___x_1792_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__5));
v___x_1793_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__2));
v___x_1794_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__12);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = l_Bool_repr___redArg(v_induction_1789_);
v___x_1797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1794_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = 0;
v___x_1799_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1793_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__9));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_box(1);
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__4));
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1792_);
v___x_1808_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_typeNames_1790_);
v___x_1809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1794_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*1, v___x_1798_);
v___x_1811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1807_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v___x_1801_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1803_);
v___x_1814_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminator_repr___redArg___closed__6));
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1792_);
v___x_1817_ = lean_obj_once(&l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4, &l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprElimInfo_repr___redArg___closed__4);
v___x_1818_ = l_Lean_Name_reprPrec(v_elimName_1791_, v___x_1795_);
v___x_1819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*1, v___x_1798_);
v___x_1821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1816_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_1823_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_1824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1821_);
v___x_1825_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_1826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1822_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set_uint8(v___x_1828_, sizeof(void*)*1, v___x_1798_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr(lean_object* v_x_1829_, lean_object* v_prec_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_instReprCustomEliminator_repr___redArg(v_x_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator_repr___boxed(lean_object* v_x_1832_, lean_object* v_prec_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Meta_instReprCustomEliminator_repr(v_x_1832_, v_prec_1833_);
lean_dec(v_prec_1833_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_unsigned_to_nat(16u);
v___x_1839_ = lean_mk_array(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__0);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2(void){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__2);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__3);
v___x_1847_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__1);
v___x_1848_ = 1;
v___x_1849_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1846_);
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*2, v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators_default(void){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators(void){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_f_1852_, lean_object* v_x1_1853_, lean_object* v_x2_1854_, lean_object* v_x3_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_apply_3(v_f_1852_, v_x1_1853_, v_x2_1854_, v_x3_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(lean_object* v_f_1857_, lean_object* v_keys_1858_, lean_object* v_vals_1859_, lean_object* v_i_1860_, lean_object* v_acc_1861_){
_start:
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_array_get_size(v_keys_1858_);
v___x_1863_ = lean_nat_dec_lt(v_i_1860_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec(v_i_1860_);
lean_dec(v_f_1857_);
return v_acc_1861_;
}
else
{
lean_object* v_k_1864_; lean_object* v_v_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_k_1864_ = lean_array_fget_borrowed(v_keys_1858_, v_i_1860_);
v_v_1865_ = lean_array_fget_borrowed(v_vals_1859_, v_i_1860_);
lean_inc(v_f_1857_);
lean_inc(v_v_1865_);
lean_inc(v_k_1864_);
v___x_1866_ = lean_apply_3(v_f_1857_, v_acc_1861_, v_k_1864_, v_v_1865_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_add(v_i_1860_, v___x_1867_);
lean_dec(v_i_1860_);
v_i_1860_ = v___x_1868_;
v_acc_1861_ = v___x_1866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg___boxed(lean_object* v_f_1870_, lean_object* v_keys_1871_, lean_object* v_vals_1872_, lean_object* v_i_1873_, lean_object* v_acc_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1870_, v_keys_1871_, v_vals_1872_, v_i_1873_, v_acc_1874_);
lean_dec_ref(v_vals_1872_);
lean_dec_ref(v_keys_1871_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(lean_object* v_f_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v_es_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_es_1879_ = lean_ctor_get(v_x_1877_, 0);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_size(v_es_1879_);
v___x_1882_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_dec(v_f_1876_);
return v_x_1878_;
}
else
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_nat_dec_le(v___x_1881_, v___x_1881_);
if (v___x_1883_ == 0)
{
if (v___x_1882_ == 0)
{
lean_dec(v_f_1876_);
return v_x_1878_;
}
else
{
size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = lean_usize_of_nat(v___x_1881_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1876_, v_es_1879_, v___x_1884_, v___x_1885_, v_x_1878_);
return v___x_1886_;
}
}
else
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_of_nat(v___x_1881_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1876_, v_es_1879_, v___x_1887_, v___x_1888_, v_x_1878_);
return v___x_1889_;
}
}
}
else
{
lean_object* v_ks_1890_; lean_object* v_vs_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_ks_1890_ = lean_ctor_get(v_x_1877_, 0);
v_vs_1891_ = lean_ctor_get(v_x_1877_, 1);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_1876_, v_ks_1890_, v_vs_1891_, v___x_1892_, v_x_1878_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(lean_object* v_f_1894_, lean_object* v_as_1895_, size_t v_i_1896_, size_t v_stop_1897_, lean_object* v_b_1898_){
_start:
{
lean_object* v___y_1900_; uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_eq(v_i_1896_, v_stop_1897_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_array_uget_borrowed(v_as_1895_, v_i_1896_);
switch(lean_obj_tag(v___x_1905_))
{
case 0:
{
lean_object* v_key_1906_; lean_object* v_val_1907_; lean_object* v___x_1908_; 
v_key_1906_ = lean_ctor_get(v___x_1905_, 0);
v_val_1907_ = lean_ctor_get(v___x_1905_, 1);
lean_inc(v_f_1894_);
lean_inc(v_val_1907_);
lean_inc(v_key_1906_);
v___x_1908_ = lean_apply_3(v_f_1894_, v_b_1898_, v_key_1906_, v_val_1907_);
v___y_1900_ = v___x_1908_;
goto v___jp_1899_;
}
case 1:
{
lean_object* v_node_1909_; lean_object* v___x_1910_; 
v_node_1909_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_f_1894_);
v___x_1910_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1894_, v_node_1909_, v_b_1898_);
v___y_1900_ = v___x_1910_;
goto v___jp_1899_;
}
default: 
{
v___y_1900_ = v_b_1898_;
goto v___jp_1899_;
}
}
}
else
{
lean_dec(v_f_1894_);
return v_b_1898_;
}
v___jp_1899_:
{
size_t v___x_1901_; size_t v___x_1902_; 
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1896_, v___x_1901_);
v_i_1896_ = v___x_1902_;
v_b_1898_ = v___y_1900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_f_1911_, lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_stop_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_i_boxed_1916_; size_t v_stop_boxed_1917_; lean_object* v_res_1918_; 
v_i_boxed_1916_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_stop_boxed_1917_ = lean_unbox_usize(v_stop_1914_);
lean_dec(v_stop_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_1911_, v_as_1912_, v_i_boxed_1916_, v_stop_boxed_1917_, v_b_1915_);
lean_dec_ref(v_as_1912_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_f_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_1919_, v_x_1920_, v_x_1921_);
lean_dec_ref(v_x_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_map_1923_, lean_object* v_f_1924_, lean_object* v_init_1925_){
_start:
{
lean_object* v___f_1926_; lean_object* v___x_1927_; 
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1926_, 0, v_f_1924_);
v___x_1927_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___f_1926_, v_map_1923_, v_init_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_map_1928_, lean_object* v_f_1929_, lean_object* v_init_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_1928_, v_f_1929_, v_init_1930_);
lean_dec_ref(v_map_1928_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
if (lean_obj_tag(v_x_1934_) == 0)
{
lean_dec(v_f_1932_);
return v_x_1933_;
}
else
{
lean_object* v_key_1935_; lean_object* v_value_1936_; lean_object* v_tail_1937_; lean_object* v___x_1938_; 
v_key_1935_ = lean_ctor_get(v_x_1934_, 0);
lean_inc(v_key_1935_);
v_value_1936_ = lean_ctor_get(v_x_1934_, 1);
lean_inc(v_value_1936_);
v_tail_1937_ = lean_ctor_get(v_x_1934_, 2);
lean_inc(v_tail_1937_);
lean_dec_ref_known(v_x_1934_, 3);
lean_inc(v_f_1932_);
v___x_1938_ = lean_apply_3(v_f_1932_, v_x_1933_, v_key_1935_, v_value_1936_);
v_x_1933_ = v___x_1938_;
v_x_1934_ = v_tail_1937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(lean_object* v_f_1940_, lean_object* v_as_1941_, size_t v_i_1942_, size_t v_stop_1943_, lean_object* v_b_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_eq(v_i_1942_, v_stop_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; 
v___x_1946_ = lean_array_uget_borrowed(v_as_1941_, v_i_1942_);
lean_inc(v___x_1946_);
lean_inc(v_f_1940_);
v___x_1947_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_1940_, v_b_1944_, v___x_1946_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1942_, v___x_1948_);
v_i_1942_ = v___x_1949_;
v_b_1944_ = v___x_1947_;
goto _start;
}
else
{
lean_dec(v_f_1940_);
return v_b_1944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_f_1951_, lean_object* v_as_1952_, lean_object* v_i_1953_, lean_object* v_stop_1954_, lean_object* v_b_1955_){
_start:
{
size_t v_i_boxed_1956_; size_t v_stop_boxed_1957_; lean_object* v_res_1958_; 
v_i_boxed_1956_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_stop_boxed_1957_ = lean_unbox_usize(v_stop_1954_);
lean_dec(v_stop_1954_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1951_, v_as_1952_, v_i_boxed_1956_, v_stop_boxed_1957_, v_b_1955_);
lean_dec_ref(v_as_1952_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(lean_object* v_f_1959_, lean_object* v_init_1960_, lean_object* v_m_1961_){
_start:
{
lean_object* v_map_u2081_1962_; lean_object* v_map_u2082_1963_; lean_object* v_buckets_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_map_u2081_1962_ = lean_ctor_get(v_m_1961_, 0);
v_map_u2082_1963_ = lean_ctor_get(v_m_1961_, 1);
v_buckets_1964_ = lean_ctor_get(v_map_u2081_1962_, 1);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get_size(v_buckets_1964_);
v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1963_, v_f_1959_, v_init_1960_);
return v___x_1968_;
}
else
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_nat_dec_le(v___x_1966_, v___x_1966_);
if (v___x_1969_ == 0)
{
if (v___x_1967_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1963_, v_f_1959_, v_init_1960_);
return v___x_1970_;
}
else
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_of_nat(v___x_1966_);
lean_inc(v_f_1959_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1959_, v_buckets_1964_, v___x_1971_, v___x_1972_, v_init_1960_);
v___x_1974_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1963_, v_f_1959_, v___x_1973_);
return v___x_1974_;
}
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1966_);
lean_inc(v_f_1959_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_1959_, v_buckets_1964_, v___x_1975_, v___x_1976_, v_init_1960_);
v___x_1978_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_u2082_1963_, v_f_1959_, v___x_1977_);
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg___boxed(lean_object* v_f_1979_, lean_object* v_init_1980_, lean_object* v_m_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_1979_, v_init_1980_, v_m_1981_);
lean_dec_ref(v_m_1981_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___lam__0(lean_object* v_es_1983_, lean_object* v_a_1984_, lean_object* v_b_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1984_);
lean_ctor_set(v___x_1986_, 1, v_b_1985_);
v___x_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v_es_1983_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(lean_object* v_m_1989_){
_start:
{
lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___f_1990_ = ((lean_object*)(l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___closed__0));
v___x_1991_ = lean_box(0);
v___x_1992_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v___f_1990_, v___x_1991_, v_m_1989_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg___boxed(lean_object* v_m_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_1993_);
lean_dec_ref(v_m_1993_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1997_) == 0)
{
lean_dec(v_x_1995_);
return v_x_1996_;
}
else
{
lean_object* v_head_1998_; lean_object* v_tail_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2008_; 
v_head_1998_ = lean_ctor_get(v_x_1997_, 0);
v_tail_1999_ = lean_ctor_get(v_x_1997_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1997_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2001_ = v_x_1997_;
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_tail_1999_);
lean_inc(v_head_1998_);
lean_dec(v_x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
lean_inc(v_x_1995_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 5);
lean_ctor_set(v___x_2001_, 1, v_x_1995_);
lean_ctor_set(v___x_2001_, 0, v_x_1996_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_x_1996_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_x_1995_);
v___x_2004_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v_head_1998_);
v_x_1996_ = v___x_2005_;
v_x_1997_ = v_tail_1999_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
if (lean_obj_tag(v_x_2009_) == 0)
{
lean_object* v___x_2011_; 
lean_dec(v_x_2010_);
v___x_2011_ = lean_box(0);
return v___x_2011_;
}
else
{
lean_object* v_tail_2012_; 
v_tail_2012_ = lean_ctor_get(v_x_2009_, 1);
if (lean_obj_tag(v_tail_2012_) == 0)
{
lean_object* v_head_2013_; 
lean_dec(v_x_2010_);
v_head_2013_ = lean_ctor_get(v_x_2009_, 0);
lean_inc(v_head_2013_);
lean_dec_ref_known(v_x_2009_, 2);
return v_head_2013_;
}
else
{
lean_object* v_head_2014_; lean_object* v___x_2015_; 
lean_inc(v_tail_2012_);
v_head_2014_ = lean_ctor_get(v_x_2009_, 0);
lean_inc(v_head_2014_);
lean_dec_ref_known(v_x_2009_, 2);
v___x_2015_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7_spec__9(v_x_2010_, v_head_2014_, v_tail_2012_);
return v___x_2015_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__0));
v___x_2019_ = lean_string_length(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__2);
v___x_2021_ = lean_nat_to_int(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2026_){
_start:
{
lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2051_; 
v_fst_2027_ = lean_ctor_get(v_x_2026_, 0);
v_snd_2028_ = lean_ctor_get(v_x_2026_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2030_ = v_x_2026_;
v_isShared_2031_ = v_isSharedCheck_2051_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snd_2028_);
lean_inc(v_fst_2027_);
lean_dec(v_x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2051_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2032_ = lean_unbox(v_fst_2027_);
lean_dec(v_fst_2027_);
v___x_2033_ = l_Bool_repr___redArg(v___x_2032_);
v___x_2034_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 1, v___x_2034_);
lean_ctor_set(v___x_2030_, 0, v___x_2033_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2037_ = l_Array_repr___at___00Lean_Meta_instReprCustomEliminator_repr_spec__0(v_snd_2028_);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
v___x_2039_ = l_List_reverse___redArg(v___x_2038_);
v___x_2040_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2041_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2043_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2041_);
v___x_2045_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2042_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = 0;
v___x_2049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*1, v___x_2048_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(lean_object* v_x_2052_){
_start:
{
lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2077_; 
v_fst_2053_ = lean_ctor_get(v_x_2052_, 0);
v_snd_2054_ = lean_ctor_get(v_x_2052_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2056_ = v_x_2052_;
v_isShared_2057_ = v_isSharedCheck_2077_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
lean_dec(v_x_2052_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2077_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_fst_2053_);
v___x_2060_ = lean_box(0);
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 1);
lean_ctor_set(v___x_2056_, 1, v___x_2060_);
lean_ctor_set(v___x_2056_, 0, v___x_2059_);
v___x_2062_ = v___x_2056_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2063_ = l_Lean_Name_reprPrec(v_snd_2054_, v___x_2058_);
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
v___x_2065_ = l_List_reverse___redArg(v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2067_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__7(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__3);
v___x_2069_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__4));
v___x_2070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2067_);
v___x_2071_ = ((lean_object*)(l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg___closed__5));
v___x_2072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = 0;
v___x_2075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*1, v___x_2074_);
return v___x_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_dec(v_x_2078_);
return v_x_2079_;
}
else
{
lean_object* v_head_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2092_; 
v_head_2081_ = lean_ctor_get(v_x_2080_, 0);
v_tail_2082_ = lean_ctor_get(v_x_2080_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2080_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2084_ = v_x_2080_;
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_head_2081_);
lean_dec(v_x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v_x_2078_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 5);
lean_ctor_set(v___x_2084_, 1, v_x_2078_);
lean_ctor_set(v___x_2084_, 0, v_x_2079_);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_x_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_x_2078_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2081_);
v___x_2089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v_x_2079_ = v___x_2089_;
v_x_2080_ = v_tail_2082_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 0)
{
lean_dec(v_x_2093_);
return v_x_2094_;
}
else
{
lean_object* v_head_2096_; lean_object* v_tail_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2107_; 
v_head_2096_ = lean_ctor_get(v_x_2095_, 0);
v_tail_2097_ = lean_ctor_get(v_x_2095_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_x_2095_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2099_ = v_x_2095_;
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_tail_2097_);
lean_inc(v_head_2096_);
lean_dec(v_x_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
lean_inc(v_x_2093_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set_tag(v___x_2099_, 5);
lean_ctor_set(v___x_2099_, 1, v_x_2093_);
lean_ctor_set(v___x_2099_, 0, v_x_2094_);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_x_2094_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_x_2093_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2096_);
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9_spec__12(v_x_2093_, v___x_2104_, v_tail_2097_);
return v___x_2105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(lean_object* v_x_2108_, lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2108_) == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_x_2109_);
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
else
{
lean_object* v_tail_2111_; 
v_tail_2111_ = lean_ctor_get(v_x_2108_, 1);
if (lean_obj_tag(v_tail_2111_) == 0)
{
lean_object* v_head_2112_; lean_object* v___x_2113_; 
lean_dec(v_x_2109_);
v_head_2112_ = lean_ctor_get(v_x_2108_, 0);
lean_inc(v_head_2112_);
lean_dec_ref_known(v_x_2108_, 2);
v___x_2113_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2112_);
return v___x_2113_;
}
else
{
lean_object* v_head_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_inc(v_tail_2111_);
v_head_2114_ = lean_ctor_get(v_x_2108_, 0);
lean_inc(v_head_2114_);
lean_dec_ref_known(v_x_2108_, 2);
v___x_2115_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_head_2114_);
v___x_2116_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3_spec__9(v_x_2109_, v___x_2115_, v_tail_2111_);
return v___x_2116_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__2));
v___x_2122_ = lean_string_length(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__3);
v___x_2124_ = lean_nat_to_int(v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(lean_object* v_a_2127_){
_start:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__1));
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2129_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__1));
v___x_2130_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__3(v_a_2127_, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__4);
v___x_2132_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg___closed__5));
v___x_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2130_);
v___x_2134_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprElimInfo_repr_spec__0___closed__6));
v___x_2135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2131_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = 0;
v___x_2138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*1, v___x_2137_);
return v___x_2138_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_unsigned_to_nat(7u);
v___x_2149_ = lean_nat_to_int(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg(lean_object* v_x_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2154_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__3));
v___x_2155_ = lean_obj_once(&l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4, &l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__4);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_x_2153_);
v___x_2158_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v___x_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_Meta_instReprCustomEliminators_repr___redArg___closed__6));
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Repr_addAppParen(v___x_2160_, v___x_2156_);
v___x_2162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2155_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = 0;
v___x_2164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2154_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20, &l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20_once, _init_l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__20);
v___x_2167_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__21));
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___x_2165_);
v___x_2169_ = ((lean_object*)(l_Lean_Meta_instReprElimAltInfo_repr___redArg___closed__22));
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2166_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*1, v___x_2163_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___redArg___boxed(lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2173_);
lean_dec_ref(v_x_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr(lean_object* v_x_2175_, lean_object* v_prec_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_instReprCustomEliminators_repr___redArg(v_x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators_repr___boxed(lean_object* v_x_2178_, lean_object* v_prec_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Meta_instReprCustomEliminators_repr(v_x_2178_, v_prec_2179_);
lean_dec(v_prec_2179_);
lean_dec_ref(v_x_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(lean_object* v_00_u03b2_2181_, lean_object* v_m_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___redArg(v_m_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0___boxed(lean_object* v_00_u03b2_2184_, lean_object* v_m_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0(v_00_u03b2_2184_, v_m_2185_);
lean_dec_ref(v_m_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(lean_object* v_a_2187_, lean_object* v_n_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___redArg(v_a_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1___boxed(lean_object* v_a_2190_, lean_object* v_n_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1(v_a_2190_, v_n_2191_);
lean_dec(v_n_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(lean_object* v_00_u03b2_2193_, lean_object* v_00_u03c3_2194_, lean_object* v_f_2195_, lean_object* v_init_2196_, lean_object* v_m_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___redArg(v_f_2195_, v_init_2196_, v_m_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2199_, lean_object* v_00_u03c3_2200_, lean_object* v_f_2201_, lean_object* v_init_2202_, lean_object* v_m_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0(v_00_u03b2_2199_, v_00_u03c3_2200_, v_f_2201_, v_init_2202_, v_m_2203_);
lean_dec_ref(v_m_2203_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___redArg(v_x_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2___boxed(lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2(v_x_2208_, v_x_2209_);
lean_dec(v_x_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2211_, lean_object* v_00_u03c3_2212_, lean_object* v_f_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__1___redArg(v_f_2213_, v_x_2214_, v_x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2217_, lean_object* v_00_u03b2_2218_, lean_object* v_map_2219_, lean_object* v_f_2220_, lean_object* v_init_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___redArg(v_map_2219_, v_f_2220_, v_init_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2223_, lean_object* v_00_u03b2_2224_, lean_object* v_map_2225_, lean_object* v_f_2226_, lean_object* v_init_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2(v_00_u03c3_2223_, v_00_u03b2_2224_, v_map_2225_, v_f_2226_, v_init_2227_);
lean_dec_ref(v_map_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2229_, lean_object* v_00_u03c3_2230_, lean_object* v_f_2231_, lean_object* v_as_2232_, size_t v_i_2233_, size_t v_stop_2234_, lean_object* v_b_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___redArg(v_f_2231_, v_as_2232_, v_i_2233_, v_stop_2234_, v_b_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2237_, lean_object* v_00_u03c3_2238_, lean_object* v_f_2239_, lean_object* v_as_2240_, lean_object* v_i_2241_, lean_object* v_stop_2242_, lean_object* v_b_2243_){
_start:
{
size_t v_i_boxed_2244_; size_t v_stop_boxed_2245_; lean_object* v_res_2246_; 
v_i_boxed_2244_ = lean_unbox_usize(v_i_2241_);
lean_dec(v_i_2241_);
v_stop_boxed_2245_ = lean_unbox_usize(v_stop_2242_);
lean_dec(v_stop_2242_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__3(v_00_u03b2_2237_, v_00_u03c3_2238_, v_f_2239_, v_as_2240_, v_i_boxed_2244_, v_stop_boxed_2245_, v_b_2243_);
lean_dec_ref(v_as_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___redArg(v_x_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6___boxed(lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Prod_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_instReprCustomEliminators_repr_spec__1_spec__2_spec__6(v_x_2250_, v_x_2251_);
lean_dec(v_x_2251_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_map_2253_, lean_object* v_f_2254_, lean_object* v_init_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2254_, v_map_2253_, v_init_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_map_2257_, lean_object* v_f_2258_, lean_object* v_init_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___redArg(v_map_2257_, v_f_2258_, v_init_2259_);
lean_dec_ref(v_map_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03c3_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_map_2263_, lean_object* v_f_2264_, lean_object* v_init_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2264_, v_map_2263_, v_init_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03c3_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_map_2269_, lean_object* v_f_2270_, lean_object* v_init_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4(v_00_u03c3_2267_, v_00_u03b2_2268_, v_map_2269_, v_f_2270_, v_init_2271_);
lean_dec_ref(v_map_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(lean_object* v_00_u03c3_2273_, lean_object* v_00_u03b1_2274_, lean_object* v_00_u03b2_2275_, lean_object* v_f_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_f_2276_, v_x_2277_, v_x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2280_, lean_object* v_00_u03b1_2281_, lean_object* v_00_u03b2_2282_, lean_object* v_f_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7(v_00_u03c3_2280_, v_00_u03b1_2281_, v_00_u03b2_2282_, v_f_2283_, v_x_2284_, v_x_2285_);
lean_dec_ref(v_x_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_2287_, lean_object* v_00_u03b2_2288_, lean_object* v_00_u03c3_2289_, lean_object* v_f_2290_, lean_object* v_as_2291_, size_t v_i_2292_, size_t v_stop_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___redArg(v_f_2290_, v_as_2291_, v_i_2292_, v_stop_2293_, v_b_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_00_u03c3_2298_, lean_object* v_f_2299_, lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_stop_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2302_);
lean_dec(v_stop_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__12(v_00_u03b1_2296_, v_00_u03b2_2297_, v_00_u03c3_2298_, v_f_2299_, v_as_2300_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(lean_object* v_00_u03c3_2307_, lean_object* v_00_u03b1_2308_, lean_object* v_00_u03b2_2309_, lean_object* v_f_2310_, lean_object* v_keys_2311_, lean_object* v_vals_2312_, lean_object* v_heq_2313_, lean_object* v_i_2314_, lean_object* v_acc_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___redArg(v_f_2310_, v_keys_2311_, v_vals_2312_, v_i_2314_, v_acc_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13___boxed(lean_object* v_00_u03c3_2317_, lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_f_2320_, lean_object* v_keys_2321_, lean_object* v_vals_2322_, lean_object* v_heq_2323_, lean_object* v_i_2324_, lean_object* v_acc_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00Lean_Meta_instReprCustomEliminators_repr_spec__0_spec__0_spec__2_spec__4_spec__7_spec__13(v_00_u03c3_2317_, v_00_u03b1_2318_, v_00_u03b2_2319_, v_f_2320_, v_keys_2321_, v_vals_2322_, v_heq_2323_, v_i_2324_, v_acc_2325_);
lean_dec_ref(v_vals_2322_);
lean_dec_ref(v_keys_2321_);
return v_res_2326_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2329_; uint64_t v___x_2330_; 
v___x_2329_ = lean_unsigned_to_nat(1723u);
v___x_2330_ = lean_uint64_of_nat(v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(lean_object* v_as_2331_, size_t v_i_2332_, size_t v_stop_2333_, uint64_t v_b_2334_){
_start:
{
uint64_t v___y_2336_; uint8_t v___x_2341_; 
v___x_2341_ = lean_usize_dec_eq(v_i_2332_, v_stop_2333_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_array_uget_borrowed(v_as_2331_, v_i_2332_);
if (lean_obj_tag(v___x_2342_) == 0)
{
uint64_t v___x_2343_; 
v___x_2343_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___closed__0);
v___y_2336_ = v___x_2343_;
goto v___jp_2335_;
}
else
{
uint64_t v_hash_2344_; 
v_hash_2344_ = lean_ctor_get_uint64(v___x_2342_, sizeof(void*)*2);
v___y_2336_ = v_hash_2344_;
goto v___jp_2335_;
}
}
else
{
return v_b_2334_;
}
v___jp_2335_:
{
uint64_t v___x_2337_; size_t v___x_2338_; size_t v___x_2339_; 
v___x_2337_ = lean_uint64_mix_hash(v_b_2334_, v___y_2336_);
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2332_, v___x_2338_);
v_i_2332_ = v___x_2339_;
v_b_2334_ = v___x_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2345_, lean_object* v_i_2346_, lean_object* v_stop_2347_, lean_object* v_b_2348_){
_start:
{
size_t v_i_boxed_2349_; size_t v_stop_boxed_2350_; uint64_t v_b_boxed_2351_; uint64_t v_res_2352_; lean_object* v_r_2353_; 
v_i_boxed_2349_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_stop_boxed_2350_ = lean_unbox_usize(v_stop_2347_);
lean_dec(v_stop_2347_);
v_b_boxed_2351_ = lean_unbox_uint64(v_b_2348_);
lean_dec_ref(v_b_2348_);
v_res_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_as_2345_, v_i_boxed_2349_, v_stop_boxed_2350_, v_b_boxed_2351_);
lean_dec_ref(v_as_2345_);
v_r_2353_ = lean_box_uint64(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
return v_x_2354_;
}
else
{
lean_object* v_key_2356_; lean_object* v_value_2357_; lean_object* v_tail_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2402_; 
v_key_2356_ = lean_ctor_get(v_x_2355_, 0);
v_value_2357_ = lean_ctor_get(v_x_2355_, 1);
v_tail_2358_ = lean_ctor_get(v_x_2355_, 2);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2360_ = v_x_2355_;
v_isShared_2361_ = v_isSharedCheck_2402_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_tail_2358_);
lean_inc(v_value_2357_);
lean_inc(v_key_2356_);
lean_dec(v_x_2355_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2402_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_fst_2362_; lean_object* v_snd_2363_; lean_object* v___x_2364_; uint64_t v___y_2366_; uint64_t v___y_2367_; uint64_t v___y_2387_; uint8_t v___x_2399_; 
v_fst_2362_ = lean_ctor_get(v_key_2356_, 0);
v_snd_2363_ = lean_ctor_get(v_key_2356_, 1);
v___x_2364_ = lean_array_get_size(v_x_2354_);
v___x_2399_ = lean_unbox(v_fst_2362_);
if (v___x_2399_ == 0)
{
uint64_t v___x_2400_; 
v___x_2400_ = 13ULL;
v___y_2387_ = v___x_2400_;
goto v___jp_2386_;
}
else
{
uint64_t v___x_2401_; 
v___x_2401_ = 11ULL;
v___y_2387_ = v___x_2401_;
goto v___jp_2386_;
}
v___jp_2365_:
{
uint64_t v___x_2368_; uint64_t v___x_2369_; uint64_t v___x_2370_; uint64_t v_fold_2371_; uint64_t v___x_2372_; uint64_t v___x_2373_; uint64_t v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2368_ = lean_uint64_mix_hash(v___y_2366_, v___y_2367_);
v___x_2369_ = 32ULL;
v___x_2370_ = lean_uint64_shift_right(v___x_2368_, v___x_2369_);
v_fold_2371_ = lean_uint64_xor(v___x_2368_, v___x_2370_);
v___x_2372_ = 16ULL;
v___x_2373_ = lean_uint64_shift_right(v_fold_2371_, v___x_2372_);
v___x_2374_ = lean_uint64_xor(v_fold_2371_, v___x_2373_);
v___x_2375_ = lean_uint64_to_usize(v___x_2374_);
v___x_2376_ = lean_usize_of_nat(v___x_2364_);
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_sub(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_usize_land(v___x_2375_, v___x_2378_);
v___x_2380_ = lean_array_uget_borrowed(v_x_2354_, v___x_2379_);
lean_inc(v___x_2380_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 2, v___x_2380_);
v___x_2382_ = v___x_2360_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_key_2356_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_value_2357_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_array_uset(v_x_2354_, v___x_2379_, v___x_2382_);
v_x_2354_ = v___x_2383_;
v_x_2355_ = v_tail_2358_;
goto _start;
}
}
v___jp_2386_:
{
uint64_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2388_ = 7ULL;
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_array_get_size(v_snd_2363_);
v___x_2391_ = lean_nat_dec_lt(v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
v___y_2366_ = v___y_2387_;
v___y_2367_ = v___x_2388_;
goto v___jp_2365_;
}
else
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_nat_dec_le(v___x_2390_, v___x_2390_);
if (v___x_2392_ == 0)
{
if (v___x_2391_ == 0)
{
v___y_2366_ = v___y_2387_;
v___y_2367_ = v___x_2388_;
goto v___jp_2365_;
}
else
{
size_t v___x_2393_; size_t v___x_2394_; uint64_t v___x_2395_; 
v___x_2393_ = ((size_t)0ULL);
v___x_2394_ = lean_usize_of_nat(v___x_2390_);
v___x_2395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2363_, v___x_2393_, v___x_2394_, v___x_2388_);
v___y_2366_ = v___y_2387_;
v___y_2367_ = v___x_2395_;
goto v___jp_2365_;
}
}
else
{
size_t v___x_2396_; size_t v___x_2397_; uint64_t v___x_2398_; 
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = lean_usize_of_nat(v___x_2390_);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2363_, v___x_2396_, v___x_2397_, v___x_2388_);
v___y_2366_ = v___y_2387_;
v___y_2367_ = v___x_2398_;
goto v___jp_2365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_i_2403_, lean_object* v_source_2404_, lean_object* v_target_2405_){
_start:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_array_get_size(v_source_2404_);
v___x_2407_ = lean_nat_dec_lt(v_i_2403_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec_ref(v_source_2404_);
lean_dec(v_i_2403_);
return v_target_2405_;
}
else
{
lean_object* v_es_2408_; lean_object* v___x_2409_; lean_object* v_source_2410_; lean_object* v_target_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_es_2408_ = lean_array_fget(v_source_2404_, v_i_2403_);
v___x_2409_ = lean_box(0);
v_source_2410_ = lean_array_fset(v_source_2404_, v_i_2403_, v___x_2409_);
v_target_2411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_target_2405_, v_es_2408_);
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_nat_add(v_i_2403_, v___x_2412_);
lean_dec(v_i_2403_);
v_i_2403_ = v___x_2413_;
v_source_2404_ = v_source_2410_;
v_target_2405_ = v_target_2411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_data_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_nbuckets_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2416_ = lean_array_get_size(v_data_2415_);
v___x_2417_ = lean_unsigned_to_nat(2u);
v_nbuckets_2418_ = lean_nat_mul(v___x_2416_, v___x_2417_);
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_mk_array(v_nbuckets_2418_, v___x_2420_);
v___x_2422_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v___x_2419_, v_data_2415_, v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_xs_2423_, lean_object* v_ys_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v_zero_2426_; uint8_t v_isZero_2427_; 
v_zero_2426_ = lean_unsigned_to_nat(0u);
v_isZero_2427_ = lean_nat_dec_eq(v_x_2425_, v_zero_2426_);
if (v_isZero_2427_ == 1)
{
lean_dec(v_x_2425_);
return v_isZero_2427_;
}
else
{
lean_object* v_one_2428_; lean_object* v_n_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_one_2428_ = lean_unsigned_to_nat(1u);
v_n_2429_ = lean_nat_sub(v_x_2425_, v_one_2428_);
lean_dec(v_x_2425_);
v___x_2430_ = lean_array_fget_borrowed(v_xs_2423_, v_n_2429_);
v___x_2431_ = lean_array_fget_borrowed(v_ys_2424_, v_n_2429_);
v___x_2432_ = lean_name_eq(v___x_2430_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_dec(v_n_2429_);
return v___x_2432_;
}
else
{
v_x_2425_ = v_n_2429_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_xs_2434_, lean_object* v_ys_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2434_, v_ys_2435_, v_x_2436_);
lean_dec_ref(v_ys_2435_);
lean_dec_ref(v_xs_2434_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_a_2439_, lean_object* v_b_2440_, lean_object* v_x_2441_){
_start:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_dec(v_b_2440_);
lean_dec_ref(v_a_2439_);
return v_x_2441_;
}
else
{
lean_object* v_key_2442_; lean_object* v_value_2443_; lean_object* v_tail_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2466_; 
v_key_2442_ = lean_ctor_get(v_x_2441_, 0);
v_value_2443_ = lean_ctor_get(v_x_2441_, 1);
v_tail_2444_ = lean_ctor_get(v_x_2441_, 2);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2446_ = v_x_2441_;
v_isShared_2447_ = v_isSharedCheck_2466_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_tail_2444_);
lean_inc(v_value_2443_);
lean_inc(v_key_2442_);
lean_dec(v_x_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2466_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; uint8_t v___x_2463_; 
v_fst_2453_ = lean_ctor_get(v_key_2442_, 0);
v_snd_2454_ = lean_ctor_get(v_key_2442_, 1);
v_fst_2455_ = lean_ctor_get(v_a_2439_, 0);
v_snd_2456_ = lean_ctor_get(v_a_2439_, 1);
v___x_2463_ = lean_unbox(v_fst_2453_);
if (v___x_2463_ == 0)
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_unbox(v_fst_2455_);
if (v___x_2464_ == 0)
{
goto v___jp_2457_;
}
else
{
goto v___jp_2448_;
}
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_unbox(v_fst_2455_);
if (v___x_2465_ == 0)
{
goto v___jp_2448_;
}
else
{
goto v___jp_2457_;
}
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2439_, v_b_2440_, v_tail_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 2, v___x_2449_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_key_2442_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_value_2443_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
v___jp_2457_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = lean_array_get_size(v_snd_2454_);
v___x_2459_ = lean_array_get_size(v_snd_2456_);
v___x_2460_ = lean_nat_dec_eq(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
goto v___jp_2448_;
}
else
{
uint8_t v___x_2461_; 
v___x_2461_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2454_, v_snd_2456_, v___x_2458_);
if (v___x_2461_ == 0)
{
goto v___jp_2448_;
}
else
{
lean_object* v___x_2462_; 
lean_del_object(v___x_2446_);
lean_dec(v_value_2443_);
lean_dec(v_key_2442_);
v___x_2462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2439_);
lean_ctor_set(v___x_2462_, 1, v_b_2440_);
lean_ctor_set(v___x_2462_, 2, v_tail_2444_);
return v___x_2462_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_a_2467_, lean_object* v_x_2468_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 0)
{
uint8_t v___x_2469_; 
v___x_2469_ = 0;
return v___x_2469_;
}
else
{
lean_object* v_key_2470_; lean_object* v_tail_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; uint8_t v___x_2483_; 
v_key_2470_ = lean_ctor_get(v_x_2468_, 0);
v_tail_2471_ = lean_ctor_get(v_x_2468_, 2);
v_fst_2472_ = lean_ctor_get(v_key_2470_, 0);
v_snd_2473_ = lean_ctor_get(v_key_2470_, 1);
v_fst_2474_ = lean_ctor_get(v_a_2467_, 0);
v_snd_2475_ = lean_ctor_get(v_a_2467_, 1);
v___x_2483_ = lean_unbox(v_fst_2472_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_unbox(v_fst_2474_);
if (v___x_2484_ == 0)
{
goto v___jp_2476_;
}
else
{
v_x_2468_ = v_tail_2471_;
goto _start;
}
}
else
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_unbox(v_fst_2474_);
if (v___x_2486_ == 0)
{
v_x_2468_ = v_tail_2471_;
goto _start;
}
else
{
goto v___jp_2476_;
}
}
v___jp_2476_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_array_get_size(v_snd_2473_);
v___x_2478_ = lean_array_get_size(v_snd_2475_);
v___x_2479_ = lean_nat_dec_eq(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
v_x_2468_ = v_tail_2471_;
goto _start;
}
else
{
uint8_t v___x_2481_; 
v___x_2481_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2473_, v_snd_2475_, v___x_2477_);
if (v___x_2481_ == 0)
{
v_x_2468_ = v_tail_2471_;
goto _start;
}
else
{
return v___x_2481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_a_2488_, lean_object* v_x_2489_){
_start:
{
uint8_t v_res_2490_; lean_object* v_r_2491_; 
v_res_2490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2488_, v_x_2489_);
lean_dec(v_x_2489_);
lean_dec_ref(v_a_2488_);
v_r_2491_ = lean_box(v_res_2490_);
return v_r_2491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(lean_object* v_m_2492_, lean_object* v_a_2493_, lean_object* v_b_2494_){
_start:
{
lean_object* v_size_2495_; lean_object* v_buckets_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2560_; 
v_size_2495_ = lean_ctor_get(v_m_2492_, 0);
v_buckets_2496_ = lean_ctor_get(v_m_2492_, 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_m_2492_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2498_ = v_m_2492_;
v_isShared_2499_ = v_isSharedCheck_2560_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_buckets_2496_);
lean_inc(v_size_2495_);
lean_dec(v_m_2492_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2560_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_fst_2500_; lean_object* v_snd_2501_; lean_object* v___x_2502_; uint64_t v___y_2504_; uint64_t v___y_2505_; uint64_t v___y_2545_; uint8_t v___x_2557_; 
v_fst_2500_ = lean_ctor_get(v_a_2493_, 0);
v_snd_2501_ = lean_ctor_get(v_a_2493_, 1);
v___x_2502_ = lean_array_get_size(v_buckets_2496_);
v___x_2557_ = lean_unbox(v_fst_2500_);
if (v___x_2557_ == 0)
{
uint64_t v___x_2558_; 
v___x_2558_ = 13ULL;
v___y_2545_ = v___x_2558_;
goto v___jp_2544_;
}
else
{
uint64_t v___x_2559_; 
v___x_2559_ = 11ULL;
v___y_2545_ = v___x_2559_;
goto v___jp_2544_;
}
v___jp_2503_:
{
uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v_fold_2509_; uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v_bkt_2518_; uint8_t v___x_2519_; 
v___x_2506_ = lean_uint64_mix_hash(v___y_2504_, v___y_2505_);
v___x_2507_ = 32ULL;
v___x_2508_ = lean_uint64_shift_right(v___x_2506_, v___x_2507_);
v_fold_2509_ = lean_uint64_xor(v___x_2506_, v___x_2508_);
v___x_2510_ = 16ULL;
v___x_2511_ = lean_uint64_shift_right(v_fold_2509_, v___x_2510_);
v___x_2512_ = lean_uint64_xor(v_fold_2509_, v___x_2511_);
v___x_2513_ = lean_uint64_to_usize(v___x_2512_);
v___x_2514_ = lean_usize_of_nat(v___x_2502_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_sub(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_usize_land(v___x_2513_, v___x_2516_);
v_bkt_2518_ = lean_array_uget_borrowed(v_buckets_2496_, v___x_2517_);
v___x_2519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2493_, v_bkt_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v_size_x27_2521_; lean_object* v___x_2522_; lean_object* v_buckets_x27_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2520_ = lean_unsigned_to_nat(1u);
v_size_x27_2521_ = lean_nat_add(v_size_2495_, v___x_2520_);
lean_dec(v_size_2495_);
lean_inc(v_bkt_2518_);
v___x_2522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2493_);
lean_ctor_set(v___x_2522_, 1, v_b_2494_);
lean_ctor_set(v___x_2522_, 2, v_bkt_2518_);
v_buckets_x27_2523_ = lean_array_uset(v_buckets_2496_, v___x_2517_, v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(4u);
v___x_2525_ = lean_nat_mul(v_size_x27_2521_, v___x_2524_);
v___x_2526_ = lean_unsigned_to_nat(3u);
v___x_2527_ = lean_nat_div(v___x_2525_, v___x_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_array_get_size(v_buckets_x27_2523_);
v___x_2529_ = lean_nat_dec_le(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
if (v___x_2529_ == 0)
{
lean_object* v_val_2530_; lean_object* v___x_2532_; 
v_val_2530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_buckets_x27_2523_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v_val_2530_);
lean_ctor_set(v___x_2498_, 0, v_size_x27_2521_);
v___x_2532_ = v___x_2498_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_size_x27_2521_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_val_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v___x_2535_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v_buckets_x27_2523_);
lean_ctor_set(v___x_2498_, 0, v_size_x27_2521_);
v___x_2535_ = v___x_2498_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_size_x27_2521_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_buckets_x27_2523_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v_buckets_x27_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_inc(v_bkt_2518_);
v___x_2537_ = lean_box(0);
v_buckets_x27_2538_ = lean_array_uset(v_buckets_2496_, v___x_2517_, v___x_2537_);
v___x_2539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2493_, v_b_2494_, v_bkt_2518_);
v___x_2540_ = lean_array_uset(v_buckets_x27_2538_, v___x_2517_, v___x_2539_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2540_);
v___x_2542_ = v___x_2498_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_size_2495_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
v___jp_2544_:
{
uint64_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2546_ = 7ULL;
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_array_get_size(v_snd_2501_);
v___x_2549_ = lean_nat_dec_lt(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
v___y_2504_ = v___y_2545_;
v___y_2505_ = v___x_2546_;
goto v___jp_2503_;
}
else
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_nat_dec_le(v___x_2548_, v___x_2548_);
if (v___x_2550_ == 0)
{
if (v___x_2549_ == 0)
{
v___y_2504_ = v___y_2545_;
v___y_2505_ = v___x_2546_;
goto v___jp_2503_;
}
else
{
size_t v___x_2551_; size_t v___x_2552_; uint64_t v___x_2553_; 
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = lean_usize_of_nat(v___x_2548_);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2501_, v___x_2551_, v___x_2552_, v___x_2546_);
v___y_2504_ = v___y_2545_;
v___y_2505_ = v___x_2553_;
goto v___jp_2503_;
}
}
else
{
size_t v___x_2554_; size_t v___x_2555_; uint64_t v___x_2556_; 
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2548_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2501_, v___x_2554_, v___x_2555_, v___x_2546_);
v___y_2504_ = v___y_2545_;
v___y_2505_ = v___x_2556_;
goto v___jp_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v_ks_2565_; lean_object* v_vs_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2605_; 
v_ks_2565_ = lean_ctor_get(v_x_2561_, 0);
v_vs_2566_ = lean_ctor_get(v_x_2561_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2568_ = v_x_2561_;
v_isShared_2569_ = v_isSharedCheck_2605_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_vs_2566_);
lean_inc(v_ks_2565_);
lean_dec(v_x_2561_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2605_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = lean_array_get_size(v_ks_2565_);
v___x_2578_ = lean_nat_dec_lt(v_x_2562_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2568_);
lean_dec(v_x_2562_);
v___x_2579_ = lean_array_push(v_ks_2565_, v_x_2563_);
v___x_2580_ = lean_array_push(v_vs_2566_, v_x_2564_);
v___x_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
return v___x_2581_;
}
else
{
lean_object* v_fst_2582_; lean_object* v_snd_2583_; lean_object* v_k_x27_2584_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2604_; 
v_fst_2582_ = lean_ctor_get(v_x_2563_, 0);
v_snd_2583_ = lean_ctor_get(v_x_2563_, 1);
v_k_x27_2584_ = lean_array_fget(v_ks_2565_, v_x_2562_);
v_fst_2585_ = lean_ctor_get(v_k_x27_2584_, 0);
v_snd_2586_ = lean_ctor_get(v_k_x27_2584_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_k_x27_2584_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2588_ = v_k_x27_2584_;
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_inc(v_fst_2585_);
lean_dec(v_k_x27_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint8_t v___y_2591_; uint8_t v___x_2601_; 
v___x_2601_ = lean_unbox(v_fst_2582_);
if (v___x_2601_ == 0)
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_unbox(v_fst_2585_);
lean_dec(v_fst_2585_);
if (v___x_2602_ == 0)
{
v___y_2591_ = v___x_2578_;
goto v___jp_2590_;
}
else
{
lean_del_object(v___x_2588_);
lean_dec(v_snd_2586_);
goto v___jp_2570_;
}
}
else
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_unbox(v_fst_2585_);
lean_dec(v_fst_2585_);
v___y_2591_ = v___x_2603_;
goto v___jp_2590_;
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
lean_del_object(v___x_2588_);
lean_dec(v_snd_2586_);
goto v___jp_2570_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = lean_array_get_size(v_snd_2583_);
v___x_2593_ = lean_array_get_size(v_snd_2586_);
v___x_2594_ = lean_nat_dec_eq(v___x_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_del_object(v___x_2588_);
lean_dec(v_snd_2586_);
goto v___jp_2570_;
}
else
{
uint8_t v___x_2595_; 
v___x_2595_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2583_, v_snd_2586_, v___x_2592_);
lean_dec(v_snd_2586_);
if (v___x_2595_ == 0)
{
lean_del_object(v___x_2588_);
goto v___jp_2570_;
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_del_object(v___x_2568_);
v___x_2596_ = lean_array_fset(v_ks_2565_, v_x_2562_, v_x_2563_);
v___x_2597_ = lean_array_fset(v_vs_2566_, v_x_2562_, v_x_2564_);
lean_dec(v_x_2562_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 1);
lean_ctor_set(v___x_2588_, 1, v___x_2597_);
lean_ctor_set(v___x_2588_, 0, v___x_2596_);
v___x_2599_ = v___x_2588_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
}
v___jp_2570_:
{
lean_object* v___x_2572_; 
if (v_isShared_2569_ == 0)
{
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_ks_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_vs_2566_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_add(v_x_2562_, v___x_2573_);
lean_dec(v_x_2562_);
v_x_2561_ = v___x_2572_;
v_x_2562_ = v___x_2574_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_2606_, lean_object* v_k_2607_, lean_object* v_v_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_n_2606_, v___x_2609_, v_k_2607_, v_v_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2612_, size_t v_x_2613_, size_t v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
if (lean_obj_tag(v_x_2612_) == 0)
{
lean_object* v_es_2617_; size_t v___x_2618_; size_t v___x_2619_; lean_object* v_j_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_es_2617_ = lean_ctor_get(v_x_2612_, 0);
v___x_2618_ = ((size_t)31ULL);
v___x_2619_ = lean_usize_land(v_x_2613_, v___x_2618_);
v_j_2620_ = lean_usize_to_nat(v___x_2619_);
v___x_2621_ = lean_array_get_size(v_es_2617_);
v___x_2622_ = lean_nat_dec_lt(v_j_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec(v_j_2620_);
lean_dec(v_x_2616_);
lean_dec_ref(v_x_2615_);
return v_x_2612_;
}
else
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2674_; 
lean_inc_ref(v_es_2617_);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_x_2612_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v_x_2612_, 0);
lean_dec(v_unused_2675_);
v___x_2624_ = v_x_2612_;
v_isShared_2625_ = v_isSharedCheck_2674_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_x_2612_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2674_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_v_2626_; lean_object* v___x_2627_; lean_object* v_xs_x27_2628_; lean_object* v___y_2630_; 
v_v_2626_ = lean_array_fget(v_es_2617_, v_j_2620_);
v___x_2627_ = lean_box(0);
v_xs_x27_2628_ = lean_array_fset(v_es_2617_, v_j_2620_, v___x_2627_);
switch(lean_obj_tag(v_v_2626_))
{
case 0:
{
lean_object* v_key_2635_; lean_object* v_val_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2659_; 
v_key_2635_ = lean_ctor_get(v_v_2626_, 0);
v_val_2636_ = lean_ctor_get(v_v_2626_, 1);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_v_2626_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2638_ = v_v_2626_;
v_isShared_2639_ = v_isSharedCheck_2659_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_val_2636_);
lean_inc(v_key_2635_);
lean_dec(v_v_2626_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2659_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; uint8_t v___y_2648_; uint8_t v___x_2656_; 
v_fst_2643_ = lean_ctor_get(v_x_2615_, 0);
v_snd_2644_ = lean_ctor_get(v_x_2615_, 1);
v_fst_2645_ = lean_ctor_get(v_key_2635_, 0);
v_snd_2646_ = lean_ctor_get(v_key_2635_, 1);
v___x_2656_ = lean_unbox(v_fst_2643_);
if (v___x_2656_ == 0)
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_unbox(v_fst_2645_);
if (v___x_2657_ == 0)
{
v___y_2648_ = v___x_2622_;
goto v___jp_2647_;
}
else
{
lean_del_object(v___x_2638_);
goto v___jp_2640_;
}
}
else
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_unbox(v_fst_2645_);
v___y_2648_ = v___x_2658_;
goto v___jp_2647_;
}
v___jp_2640_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2635_, v_val_2636_, v_x_2615_, v_x_2616_);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
v___y_2630_ = v___x_2642_;
goto v___jp_2629_;
}
v___jp_2647_:
{
if (v___y_2648_ == 0)
{
lean_del_object(v___x_2638_);
goto v___jp_2640_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_array_get_size(v_snd_2644_);
v___x_2650_ = lean_array_get_size(v_snd_2646_);
v___x_2651_ = lean_nat_dec_eq(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_del_object(v___x_2638_);
goto v___jp_2640_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_2644_, v_snd_2646_, v___x_2649_);
if (v___x_2652_ == 0)
{
lean_del_object(v___x_2638_);
goto v___jp_2640_;
}
else
{
lean_object* v___x_2654_; 
lean_dec(v_val_2636_);
lean_dec(v_key_2635_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v_x_2616_);
lean_ctor_set(v___x_2638_, 0, v_x_2615_);
v___x_2654_ = v___x_2638_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_x_2615_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_x_2616_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
v___y_2630_ = v___x_2654_;
goto v___jp_2629_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_node_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2672_; 
v_node_2660_ = lean_ctor_get(v_v_2626_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_v_2626_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2662_ = v_v_2626_;
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_node_2660_);
lean_dec(v_v_2626_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
size_t v___x_2664_; size_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2664_ = ((size_t)5ULL);
v___x_2665_ = lean_usize_shift_right(v_x_2613_, v___x_2664_);
v___x_2666_ = ((size_t)1ULL);
v___x_2667_ = lean_usize_add(v_x_2614_, v___x_2666_);
v___x_2668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_node_2660_, v___x_2665_, v___x_2667_, v_x_2615_, v_x_2616_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2668_);
v___x_2670_ = v___x_2662_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
v___y_2630_ = v___x_2670_;
goto v___jp_2629_;
}
}
}
default: 
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_x_2615_);
lean_ctor_set(v___x_2673_, 1, v_x_2616_);
v___y_2630_ = v___x_2673_;
goto v___jp_2629_;
}
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_array_fset(v_xs_x27_2628_, v_j_2620_, v___y_2630_);
lean_dec(v_j_2620_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2631_);
v___x_2633_ = v___x_2624_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
else
{
lean_object* v_ks_2676_; lean_object* v_vs_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2697_; 
v_ks_2676_ = lean_ctor_get(v_x_2612_, 0);
v_vs_2677_ = lean_ctor_get(v_x_2612_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_x_2612_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2679_ = v_x_2612_;
v_isShared_2680_ = v_isSharedCheck_2697_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_vs_2677_);
lean_inc(v_ks_2676_);
lean_dec(v_x_2612_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2697_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_ks_2676_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_vs_2677_);
v___x_2682_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v_newNode_2683_; uint8_t v___y_2685_; size_t v___x_2691_; uint8_t v___x_2692_; 
v_newNode_2683_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v___x_2682_, v_x_2615_, v_x_2616_);
v___x_2691_ = ((size_t)7ULL);
v___x_2692_ = lean_usize_dec_le(v___x_2691_, v_x_2614_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2683_);
v___x_2694_ = lean_unsigned_to_nat(4u);
v___x_2695_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
lean_dec(v___x_2693_);
v___y_2685_ = v___x_2695_;
goto v___jp_2684_;
}
else
{
v___y_2685_ = v___x_2692_;
goto v___jp_2684_;
}
v___jp_2684_:
{
if (v___y_2685_ == 0)
{
lean_object* v_ks_2686_; lean_object* v_vs_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_ks_2686_ = lean_ctor_get(v_newNode_2683_, 0);
lean_inc_ref(v_ks_2686_);
v_vs_2687_ = lean_ctor_get(v_newNode_2683_, 1);
lean_inc_ref(v_vs_2687_);
lean_dec_ref(v_newNode_2683_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2690_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2614_, v_ks_2686_, v_vs_2687_, v___x_2688_, v___x_2689_);
lean_dec_ref(v_vs_2687_);
lean_dec_ref(v_ks_2686_);
return v___x_2690_;
}
else
{
return v_newNode_2683_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_2698_, lean_object* v_keys_2699_, lean_object* v_vals_2700_, lean_object* v_i_2701_, lean_object* v_entries_2702_){
_start:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = lean_array_get_size(v_keys_2699_);
v___x_2704_ = lean_nat_dec_lt(v_i_2701_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_dec(v_i_2701_);
return v_entries_2702_;
}
else
{
lean_object* v_k_2705_; lean_object* v_fst_2706_; lean_object* v_snd_2707_; lean_object* v_v_2708_; uint64_t v___y_2710_; uint64_t v___y_2711_; uint64_t v___y_2724_; uint8_t v___x_2736_; 
v_k_2705_ = lean_array_fget_borrowed(v_keys_2699_, v_i_2701_);
v_fst_2706_ = lean_ctor_get(v_k_2705_, 0);
v_snd_2707_ = lean_ctor_get(v_k_2705_, 1);
v_v_2708_ = lean_array_fget_borrowed(v_vals_2700_, v_i_2701_);
v___x_2736_ = lean_unbox(v_fst_2706_);
if (v___x_2736_ == 0)
{
uint64_t v___x_2737_; 
v___x_2737_ = 13ULL;
v___y_2724_ = v___x_2737_;
goto v___jp_2723_;
}
else
{
uint64_t v___x_2738_; 
v___x_2738_ = 11ULL;
v___y_2724_ = v___x_2738_;
goto v___jp_2723_;
}
v___jp_2709_:
{
uint64_t v___x_2712_; size_t v_h_2713_; size_t v___x_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; size_t v_h_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2712_ = lean_uint64_mix_hash(v___y_2710_, v___y_2711_);
v_h_2713_ = lean_uint64_to_usize(v___x_2712_);
v___x_2714_ = ((size_t)5ULL);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_sub(v_depth_2698_, v___x_2716_);
v___x_2718_ = lean_usize_mul(v___x_2714_, v___x_2717_);
v_h_2719_ = lean_usize_shift_right(v_h_2713_, v___x_2718_);
v___x_2720_ = lean_nat_add(v_i_2701_, v___x_2715_);
lean_dec(v_i_2701_);
lean_inc(v_v_2708_);
lean_inc(v_k_2705_);
v___x_2721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_entries_2702_, v_h_2719_, v_depth_2698_, v_k_2705_, v_v_2708_);
v_i_2701_ = v___x_2720_;
v_entries_2702_ = v___x_2721_;
goto _start;
}
v___jp_2723_:
{
uint64_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2725_ = 7ULL;
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = lean_array_get_size(v_snd_2707_);
v___x_2728_ = lean_nat_dec_lt(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
v___y_2710_ = v___y_2724_;
v___y_2711_ = v___x_2725_;
goto v___jp_2709_;
}
else
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_nat_dec_le(v___x_2727_, v___x_2727_);
if (v___x_2729_ == 0)
{
if (v___x_2728_ == 0)
{
v___y_2710_ = v___y_2724_;
v___y_2711_ = v___x_2725_;
goto v___jp_2709_;
}
else
{
size_t v___x_2730_; size_t v___x_2731_; uint64_t v___x_2732_; 
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = lean_usize_of_nat(v___x_2727_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2707_, v___x_2730_, v___x_2731_, v___x_2725_);
v___y_2710_ = v___y_2724_;
v___y_2711_ = v___x_2732_;
goto v___jp_2709_;
}
}
else
{
size_t v___x_2733_; size_t v___x_2734_; uint64_t v___x_2735_; 
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_of_nat(v___x_2727_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2707_, v___x_2733_, v___x_2734_, v___x_2725_);
v___y_2710_ = v___y_2724_;
v___y_2711_ = v___x_2735_;
goto v___jp_2709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_2739_, lean_object* v_keys_2740_, lean_object* v_vals_2741_, lean_object* v_i_2742_, lean_object* v_entries_2743_){
_start:
{
size_t v_depth_boxed_2744_; lean_object* v_res_2745_; 
v_depth_boxed_2744_ = lean_unbox_usize(v_depth_2739_);
lean_dec(v_depth_2739_);
v_res_2745_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_2744_, v_keys_2740_, v_vals_2741_, v_i_2742_, v_entries_2743_);
lean_dec_ref(v_vals_2741_);
lean_dec_ref(v_keys_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
size_t v_x_2146__boxed_2751_; size_t v_x_2147__boxed_2752_; lean_object* v_res_2753_; 
v_x_2146__boxed_2751_ = lean_unbox_usize(v_x_2747_);
lean_dec(v_x_2747_);
v_x_2147__boxed_2752_ = lean_unbox_usize(v_x_2748_);
lean_dec(v_x_2748_);
v_res_2753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2746_, v_x_2146__boxed_2751_, v_x_2147__boxed_2752_, v_x_2749_, v_x_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
uint64_t v___y_2758_; uint64_t v___y_2759_; lean_object* v_fst_2764_; lean_object* v_snd_2765_; uint64_t v___y_2767_; uint8_t v___x_2779_; 
v_fst_2764_ = lean_ctor_get(v_x_2755_, 0);
v_snd_2765_ = lean_ctor_get(v_x_2755_, 1);
v___x_2779_ = lean_unbox(v_fst_2764_);
if (v___x_2779_ == 0)
{
uint64_t v___x_2780_; 
v___x_2780_ = 13ULL;
v___y_2767_ = v___x_2780_;
goto v___jp_2766_;
}
else
{
uint64_t v___x_2781_; 
v___x_2781_ = 11ULL;
v___y_2767_ = v___x_2781_;
goto v___jp_2766_;
}
v___jp_2757_:
{
uint64_t v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = lean_uint64_mix_hash(v___y_2758_, v___y_2759_);
v___x_2761_ = lean_uint64_to_usize(v___x_2760_);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2754_, v___x_2761_, v___x_2762_, v_x_2755_, v_x_2756_);
return v___x_2763_;
}
v___jp_2766_:
{
uint64_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2768_ = 7ULL;
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_array_get_size(v_snd_2765_);
v___x_2771_ = lean_nat_dec_lt(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___x_2768_;
goto v___jp_2757_;
}
else
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_nat_dec_le(v___x_2770_, v___x_2770_);
if (v___x_2772_ == 0)
{
if (v___x_2771_ == 0)
{
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___x_2768_;
goto v___jp_2757_;
}
else
{
size_t v___x_2773_; size_t v___x_2774_; uint64_t v___x_2775_; 
v___x_2773_ = ((size_t)0ULL);
v___x_2774_ = lean_usize_of_nat(v___x_2770_);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2765_, v___x_2773_, v___x_2774_, v___x_2768_);
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___x_2775_;
goto v___jp_2757_;
}
}
else
{
size_t v___x_2776_; size_t v___x_2777_; uint64_t v___x_2778_; 
v___x_2776_ = ((size_t)0ULL);
v___x_2777_ = lean_usize_of_nat(v___x_2770_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_2765_, v___x_2776_, v___x_2777_, v___x_2768_);
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___x_2778_;
goto v___jp_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
uint8_t v_stage_u2081_2785_; 
v_stage_u2081_2785_ = lean_ctor_get_uint8(v_x_2782_, sizeof(void*)*2);
if (v_stage_u2081_2785_ == 0)
{
lean_object* v_map_u2081_2786_; lean_object* v_map_u2082_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2795_; 
v_map_u2081_2786_ = lean_ctor_get(v_x_2782_, 0);
v_map_u2082_2787_ = lean_ctor_get(v_x_2782_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2789_ = v_x_2782_;
v_isShared_2790_ = v_isSharedCheck_2795_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_map_u2082_2787_);
lean_inc(v_map_u2081_2786_);
lean_dec(v_x_2782_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2795_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2791_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_map_u2082_2787_, v_x_2783_, v_x_2784_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 1, v___x_2791_);
v___x_2793_ = v___x_2789_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_map_u2081_2786_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, sizeof(void*)*2, v_stage_u2081_2785_);
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
lean_object* v_map_u2081_2796_; lean_object* v_map_u2082_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2805_; 
v_map_u2081_2796_ = lean_ctor_get(v_x_2782_, 0);
v_map_u2082_2797_ = lean_ctor_get(v_x_2782_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2799_ = v_x_2782_;
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_map_u2082_2797_);
lean_inc(v_map_u2081_2796_);
lean_dec(v_x_2782_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_map_u2081_2796_, v_x_2783_, v_x_2784_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_map_u2082_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2804_, sizeof(void*)*2, v_stage_u2081_2785_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* v_es_2806_, lean_object* v_e_2807_){
_start:
{
uint8_t v_induction_2808_; lean_object* v_typeNames_2809_; lean_object* v_elimName_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_induction_2808_ = lean_ctor_get_uint8(v_e_2807_, sizeof(void*)*2);
v_typeNames_2809_ = lean_ctor_get(v_e_2807_, 0);
lean_inc_ref(v_typeNames_2809_);
v_elimName_2810_ = lean_ctor_get(v_e_2807_, 1);
lean_inc(v_elimName_2810_);
lean_dec_ref(v_e_2807_);
v___x_2811_ = lean_box(v_induction_2808_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v_typeNames_2809_);
v___x_2813_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_es_2806_, v___x_2812_, v_elimName_2810_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* v_00_u03b2_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(v_x_2815_, v_x_2816_, v_x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* v_00_u03b2_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(v_x_2820_, v_x_2821_, v_x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1(lean_object* v_00_u03b2_2824_, lean_object* v_m_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1___redArg(v_m_2825_, v_a_2826_, v_b_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2829_, lean_object* v_x_2830_, size_t v_x_2831_, size_t v_x_2832_, lean_object* v_x_2833_, lean_object* v_x_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___redArg(v_x_2830_, v_x_2831_, v_x_2832_, v_x_2833_, v_x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_){
_start:
{
size_t v_x_2478__boxed_2842_; size_t v_x_2479__boxed_2843_; lean_object* v_res_2844_; 
v_x_2478__boxed_2842_ = lean_unbox_usize(v_x_2838_);
lean_dec(v_x_2838_);
v_x_2479__boxed_2843_ = lean_unbox_usize(v_x_2839_);
lean_dec(v_x_2839_);
v_res_2844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1(v_00_u03b2_2836_, v_x_2837_, v_x_2478__boxed_2842_, v_x_2479__boxed_2843_, v_x_2840_, v_x_2841_);
return v_res_2844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2845_, lean_object* v_a_2846_, lean_object* v_x_2847_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___redArg(v_a_2846_, v_x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2849_, lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
uint8_t v_res_2852_; lean_object* v_r_2853_; 
v_res_2852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__4(v_00_u03b2_2849_, v_a_2850_, v_x_2851_);
lean_dec(v_x_2851_);
lean_dec_ref(v_a_2850_);
v_r_2853_ = lean_box(v_res_2852_);
return v_r_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2854_, lean_object* v_data_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5___redArg(v_data_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_2857_, lean_object* v_a_2858_, lean_object* v_b_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__6___redArg(v_a_2858_, v_b_2859_, v_x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_2862_, lean_object* v_ys_2863_, lean_object* v_hsz_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
uint8_t v___x_2867_; 
v___x_2867_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_xs_2862_, v_ys_2863_, v_x_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_2868_, lean_object* v_ys_2869_, lean_object* v_hsz_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2(v_xs_2868_, v_ys_2869_, v_hsz_2870_, v_x_2871_, v_x_2872_);
lean_dec_ref(v_ys_2869_);
lean_dec_ref(v_xs_2868_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2875_, lean_object* v_n_2876_, lean_object* v_k_2877_, lean_object* v_v_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2876_, v_k_2877_, v_v_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2880_, size_t v_depth_2881_, lean_object* v_keys_2882_, lean_object* v_vals_2883_, lean_object* v_heq_2884_, lean_object* v_i_2885_, lean_object* v_entries_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_2881_, v_keys_2882_, v_vals_2883_, v_i_2885_, v_entries_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2888_, lean_object* v_depth_2889_, lean_object* v_keys_2890_, lean_object* v_vals_2891_, lean_object* v_heq_2892_, lean_object* v_i_2893_, lean_object* v_entries_2894_){
_start:
{
size_t v_depth_boxed_2895_; lean_object* v_res_2896_; 
v_depth_boxed_2895_ = lean_unbox_usize(v_depth_2889_);
lean_dec(v_depth_2889_);
v_res_2896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2888_, v_depth_boxed_2895_, v_keys_2890_, v_vals_2891_, v_heq_2892_, v_i_2893_, v_entries_2894_);
lean_dec_ref(v_vals_2891_);
lean_dec_ref(v_keys_2890_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2897_, lean_object* v_i_2898_, lean_object* v_source_2899_, lean_object* v_target_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9___redArg(v_i_2898_, v_source_2899_, v_target_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2903_, v_x_2904_, v_x_2905_, v_x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11(lean_object* v_00_u03b2_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__1_spec__5_spec__9_spec__11___redArg(v_x_2909_, v_x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_2912_){
_start:
{
uint8_t v_stage_u2081_2913_; 
v_stage_u2081_2913_ = lean_ctor_get_uint8(v_m_2912_, sizeof(void*)*2);
if (v_stage_u2081_2913_ == 0)
{
return v_m_2912_;
}
else
{
lean_object* v_map_u2081_2914_; lean_object* v_map_u2082_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2923_; 
v_map_u2081_2914_ = lean_ctor_get(v_m_2912_, 0);
v_map_u2082_2915_ = lean_ctor_get(v_m_2912_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_m_2912_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2917_ = v_m_2912_;
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_map_u2082_2915_);
lean_inc(v_map_u2081_2914_);
lean_dec(v_m_2912_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
uint8_t v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = 0;
if (v_isShared_2918_ == 0)
{
v___x_2921_ = v___x_2917_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_map_u2081_2914_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_map_u2082_2915_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*2, v___x_2919_);
return v___x_2921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_2924_, lean_object* v_m_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_SMap_switch___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__spec__0___redArg(v_m_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(lean_object* v_x_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2928_);
lean_inc_ref_n(v___x_2929_, 2);
v___x_2930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
lean_ctor_set(v___x_2930_, 2, v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_x_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(v_x_2931_, v_a_2932_);
lean_dec_ref(v_x_2931_);
return v_res_2933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___f_2944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___f_2945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2946_ = lean_obj_once(&l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4, &l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4_once, _init_l_Lean_Meta_instInhabitedCustomEliminators_default___closed__4);
v___x_2947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_));
v___x_2949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2947_);
lean_ctor_set(v___x_2949_, 2, v___x_2946_);
lean_ctor_set(v___x_2949_, 3, v___f_2945_);
lean_ctor_set(v___x_2949_, 4, v___f_2944_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_);
v___x_2952_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2____boxed(lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_1692558223____hygCtx___hyg_2_();
return v_res_2954_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* v_x_2955_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = 0;
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* v_x_2957_){
_start:
{
uint8_t v_res_2958_; lean_object* v_r_2959_; 
v_res_2958_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(v_x_2957_);
lean_dec(v_x_2957_);
v_r_2959_ = lean_box(v_res_2958_);
return v_r_2959_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* v_fvarId_2960_, lean_object* v_x_2961_){
_start:
{
uint8_t v___x_2962_; 
v___x_2962_ = l_Lean_instBEqFVarId_beq(v_fvarId_2960_, v_x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_2963_, lean_object* v_x_2964_){
_start:
{
uint8_t v_res_2965_; lean_object* v_r_2966_; 
v_res_2965_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(v_fvarId_2963_, v_x_2964_);
lean_dec(v_x_2964_);
lean_dec(v_fvarId_2963_);
v_r_2966_ = lean_box(v_res_2965_);
return v_r_2966_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_unsigned_to_nat(16u);
v___x_2970_ = lean_mk_array(v___x_2969_, v___x_2968_);
return v___x_2970_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__1);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* v_e_2974_, lean_object* v_fvarId_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; uint8_t v_fst_2980_; lean_object* v_mctx_2981_; lean_object* v___y_2999_; lean_object* v_mctx_3004_; lean_object* v___f_3005_; lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_2978_ = lean_st_ref_get(v___y_2976_);
v_mctx_3004_ = lean_ctor_get(v___x_2978_, 0);
lean_inc_ref_n(v_mctx_3004_, 2);
lean_dec(v___x_2978_);
v___f_3005_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__0));
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3006_, 0, v_fvarId_2975_);
v___x_3007_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___closed__2);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v_mctx_3004_);
v___x_3009_ = l_Lean_Expr_hasFVar(v_e_2974_);
if (v___x_3009_ == 0)
{
uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Expr_hasMVar(v_e_2974_);
if (v___x_3010_ == 0)
{
lean_dec_ref_known(v___x_3008_, 2);
lean_dec_ref(v___f_3006_);
lean_dec_ref(v_e_2974_);
v_fst_2980_ = v___x_3010_;
v_mctx_2981_ = v_mctx_3004_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3011_; 
lean_dec_ref(v_mctx_3004_);
v___x_3011_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3006_, v___f_3005_, v_e_2974_, v___x_3008_);
v___y_2999_ = v___x_3011_;
goto v___jp_2998_;
}
}
else
{
lean_object* v___x_3012_; 
lean_dec_ref(v_mctx_3004_);
v___x_3012_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3006_, v___f_3005_, v_e_2974_, v___x_3008_);
v___y_2999_ = v___x_3012_;
goto v___jp_2998_;
}
v___jp_2979_:
{
lean_object* v___x_2982_; lean_object* v_cache_2983_; lean_object* v_zetaDeltaFVarIds_2984_; lean_object* v_postponed_2985_; lean_object* v_diag_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2996_; 
v___x_2982_ = lean_st_ref_take(v___y_2976_);
v_cache_2983_ = lean_ctor_get(v___x_2982_, 1);
v_zetaDeltaFVarIds_2984_ = lean_ctor_get(v___x_2982_, 2);
v_postponed_2985_ = lean_ctor_get(v___x_2982_, 3);
v_diag_2986_ = lean_ctor_get(v___x_2982_, 4);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2982_, 0);
lean_dec(v_unused_2997_);
v___x_2988_ = v___x_2982_;
v_isShared_2989_ = v_isSharedCheck_2996_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_diag_2986_);
lean_inc(v_postponed_2985_);
lean_inc(v_zetaDeltaFVarIds_2984_);
lean_inc(v_cache_2983_);
lean_dec(v___x_2982_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2996_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v_mctx_2981_);
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_mctx_2981_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_cache_2983_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_zetaDeltaFVarIds_2984_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v_postponed_2985_);
lean_ctor_set(v_reuseFailAlloc_2995_, 4, v_diag_2986_);
v___x_2991_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_st_ref_set(v___y_2976_, v___x_2991_);
v___x_2993_ = lean_box(v_fst_2980_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
}
v___jp_2998_:
{
lean_object* v_snd_3000_; lean_object* v_fst_3001_; lean_object* v_mctx_3002_; uint8_t v___x_3003_; 
v_snd_3000_ = lean_ctor_get(v___y_2999_, 1);
lean_inc(v_snd_3000_);
v_fst_3001_ = lean_ctor_get(v___y_2999_, 0);
lean_inc(v_fst_3001_);
lean_dec_ref(v___y_2999_);
v_mctx_3002_ = lean_ctor_get(v_snd_3000_, 1);
lean_inc_ref(v_mctx_3002_);
lean_dec(v_snd_3000_);
v___x_3003_ = lean_unbox(v_fst_3001_);
lean_dec(v_fst_3001_);
v_fst_2980_ = v___x_3003_;
v_mctx_2981_ = v_mctx_3002_;
goto v___jp_2979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* v_e_3013_, lean_object* v_fvarId_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3013_, v_fvarId_3014_, v___y_3015_);
lean_dec(v___y_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(lean_object* v_e_3018_, lean_object* v_fvarId_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_e_3018_, v_fvarId_3019_, v___y_3021_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* v_e_3026_, lean_object* v_fvarId_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0(v_e_3026_, v_fvarId_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* v_upperBound_3037_, lean_object* v___x_3038_, lean_object* v_xs_3039_, lean_object* v___x_3040_, lean_object* v_a_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_nat_dec_lt(v_a_3041_, v_upperBound_3037_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec(v_a_3041_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_b_3042_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec_ref(v_b_3042_);
v___x_3050_ = l_Lean_instInhabitedExpr;
v___x_3051_ = lean_array_fget_borrowed(v___x_3038_, v_a_3041_);
v___x_3052_ = lean_array_get_borrowed(v___x_3050_, v_xs_3039_, v___x_3051_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3044_);
lean_inc_ref(v___y_3043_);
lean_inc(v___x_3052_);
v___x_3053_ = lean_infer_type(v___x_3052_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_Lean_Expr_fvarId_x21(v___x_3040_);
v___x_3056_ = l_Lean_exprDependsOn___at___00Lean_Meta_mkCustomEliminator_spec__0___redArg(v_a_3054_, v___x_3055_, v___y_3044_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3072_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3072_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3072_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_unbox(v_a_3057_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_del_object(v___x_3059_);
lean_dec(v_a_3057_);
v___x_3063_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_nat_add(v_a_3041_, v___x_3064_);
lean_dec(v_a_3041_);
v_a_3041_ = v___x_3065_;
v_b_3042_ = v___x_3063_;
goto _start;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_dec(v_a_3041_);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3057_);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3061_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3068_);
v___x_3070_ = v___x_3059_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_3041_);
v_a_3073_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3056_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3056_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3041_);
v_a_3081_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3053_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3053_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* v_upperBound_3089_, lean_object* v___x_3090_, lean_object* v_xs_3091_, lean_object* v___x_3092_, lean_object* v_a_3093_, lean_object* v_b_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3089_, v___x_3090_, v_xs_3091_, v___x_3092_, v_a_3093_, v_b_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v_xs_3091_);
lean_dec_ref(v___x_3090_);
lean_dec(v_upperBound_3089_);
return v_res_3100_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__0));
v___x_3103_ = l_Lean_stringToMessageData(v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* v_upperBound_3104_, lean_object* v___x_3105_, lean_object* v___x_3106_, lean_object* v_xs_3107_, lean_object* v_a_3108_, lean_object* v_b_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_a_3116_; uint8_t v___x_3120_; 
v___x_3120_ = lean_nat_dec_lt(v_a_3108_, v_upperBound_3104_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_dec(v_a_3108_);
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3109_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3122_ = l_Lean_instInhabitedExpr;
v___x_3123_ = lean_unsigned_to_nat(1u);
v___x_3124_ = lean_nat_add(v_a_3108_, v___x_3123_);
v___x_3125_ = lean_array_fget_borrowed(v___x_3106_, v_a_3108_);
v___x_3126_ = lean_array_get_borrowed(v___x_3122_, v_xs_3107_, v___x_3125_);
v___x_3153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg___closed__0));
v___x_3154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v___x_3105_, v___x_3106_, v_xs_3107_, v___x_3126_, v___x_3124_, v___x_3153_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v_fst_3156_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v_fst_3156_ = lean_ctor_get(v_a_3155_, 0);
lean_inc(v_fst_3156_);
lean_dec(v_a_3155_);
if (lean_obj_tag(v_fst_3156_) == 0)
{
goto v___jp_3127_;
}
else
{
lean_object* v_val_3157_; uint8_t v___x_3158_; 
v_val_3157_ = lean_ctor_get(v_fst_3156_, 0);
lean_inc(v_val_3157_);
lean_dec_ref_known(v_fst_3156_, 1);
v___x_3158_ = lean_unbox(v_val_3157_);
lean_dec(v_val_3157_);
if (v___x_3158_ == 0)
{
goto v___jp_3127_;
}
else
{
v_a_3116_ = v_b_3109_;
goto v___jp_3115_;
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v_b_3109_);
lean_dec(v_a_3108_);
v_a_3159_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3154_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3154_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
v___jp_3127_:
{
lean_object* v___x_3128_; 
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3111_);
lean_inc_ref(v___y_3110_);
lean_inc(v___x_3126_);
v___x_3128_ = lean_infer_type(v___x_3126_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3130_ = l_Lean_Expr_getAppFn(v_a_3129_);
if (lean_obj_tag(v___x_3130_) == 4)
{
lean_object* v_declName_3131_; lean_object* v___x_3132_; 
lean_dec(v_a_3129_);
v_declName_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_declName_3131_);
lean_dec_ref_known(v___x_3130_, 2);
v___x_3132_ = lean_array_push(v_b_3109_, v_declName_3131_);
v_a_3116_ = v___x_3132_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec_ref(v___x_3130_);
v___x_3133_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___closed__1);
v___x_3134_ = l_Lean_indentExpr(v_a_3129_);
v___x_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v___x_3135_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_dec_ref_known(v___x_3136_, 1);
v_a_3116_ = v_b_3109_;
goto v___jp_3115_;
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_b_3109_);
lean_dec(v_a_3108_);
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v_b_3109_);
lean_dec(v_a_3108_);
v_a_3145_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3128_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3128_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_add(v_a_3108_, v___x_3117_);
lean_dec(v_a_3108_);
v_a_3108_ = v___x_3118_;
v_b_3109_ = v_a_3116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* v_upperBound_3167_, lean_object* v___x_3168_, lean_object* v___x_3169_, lean_object* v_xs_3170_, lean_object* v_a_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3167_, v___x_3168_, v___x_3169_, v_xs_3170_, v_a_3171_, v_b_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_xs_3170_);
lean_dec_ref(v___x_3169_);
lean_dec(v___x_3168_);
lean_dec(v_upperBound_3167_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* v_a_3179_, uint8_t v_induction_3180_, lean_object* v_elimName_3181_, lean_object* v_xs_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_targetsPos_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_targetsPos_3189_ = lean_ctor_get(v_a_3179_, 3);
v___x_3190_ = lean_array_get_size(v_targetsPos_3189_);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = ((lean_object*)(l_Lean_Meta_addImplicitTargets___closed__0));
v___x_3193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v___x_3190_, v___x_3190_, v_targetsPos_3189_, v_xs_3182_, v___x_3191_, v___x_3192_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3202_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3198_, 0, v_a_3194_);
lean_ctor_set(v___x_3198_, 1, v_elimName_3181_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*2, v_induction_3180_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_elimName_3181_);
v_a_3203_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3193_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3193_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* v_a_3211_, lean_object* v_induction_3212_, lean_object* v_elimName_3213_, lean_object* v_xs_3214_, lean_object* v_x_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v_induction_boxed_3221_; lean_object* v_res_3222_; 
v_induction_boxed_3221_ = lean_unbox(v_induction_3212_);
v_res_3222_ = l_Lean_Meta_mkCustomEliminator___lam__0(v_a_3211_, v_induction_boxed_3221_, v_elimName_3213_, v_xs_3214_, v_x_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec_ref(v_x_3215_);
lean_dec_ref(v_xs_3214_);
lean_dec_ref(v_a_3211_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_3223_, lean_object* v_msg_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_fileName_3230_; lean_object* v_fileMap_3231_; lean_object* v_options_3232_; lean_object* v_currRecDepth_3233_; lean_object* v_maxRecDepth_3234_; lean_object* v_ref_3235_; lean_object* v_currNamespace_3236_; lean_object* v_openDecls_3237_; lean_object* v_initHeartbeats_3238_; lean_object* v_maxHeartbeats_3239_; lean_object* v_quotContext_3240_; lean_object* v_currMacroScope_3241_; uint8_t v_diag_3242_; lean_object* v_cancelTk_x3f_3243_; uint8_t v_suppressElabErrors_3244_; lean_object* v_inheritedTraceOptions_3245_; lean_object* v_ref_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_fileName_3230_ = lean_ctor_get(v___y_3227_, 0);
v_fileMap_3231_ = lean_ctor_get(v___y_3227_, 1);
v_options_3232_ = lean_ctor_get(v___y_3227_, 2);
v_currRecDepth_3233_ = lean_ctor_get(v___y_3227_, 3);
v_maxRecDepth_3234_ = lean_ctor_get(v___y_3227_, 4);
v_ref_3235_ = lean_ctor_get(v___y_3227_, 5);
v_currNamespace_3236_ = lean_ctor_get(v___y_3227_, 6);
v_openDecls_3237_ = lean_ctor_get(v___y_3227_, 7);
v_initHeartbeats_3238_ = lean_ctor_get(v___y_3227_, 8);
v_maxHeartbeats_3239_ = lean_ctor_get(v___y_3227_, 9);
v_quotContext_3240_ = lean_ctor_get(v___y_3227_, 10);
v_currMacroScope_3241_ = lean_ctor_get(v___y_3227_, 11);
v_diag_3242_ = lean_ctor_get_uint8(v___y_3227_, sizeof(void*)*14);
v_cancelTk_x3f_3243_ = lean_ctor_get(v___y_3227_, 12);
v_suppressElabErrors_3244_ = lean_ctor_get_uint8(v___y_3227_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3245_ = lean_ctor_get(v___y_3227_, 13);
v_ref_3246_ = l_Lean_replaceRef(v_ref_3223_, v_ref_3235_);
lean_inc_ref(v_inheritedTraceOptions_3245_);
lean_inc(v_cancelTk_x3f_3243_);
lean_inc(v_currMacroScope_3241_);
lean_inc(v_quotContext_3240_);
lean_inc(v_maxHeartbeats_3239_);
lean_inc(v_initHeartbeats_3238_);
lean_inc(v_openDecls_3237_);
lean_inc(v_currNamespace_3236_);
lean_inc(v_maxRecDepth_3234_);
lean_inc(v_currRecDepth_3233_);
lean_inc_ref(v_options_3232_);
lean_inc_ref(v_fileMap_3231_);
lean_inc_ref(v_fileName_3230_);
v___x_3247_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3247_, 0, v_fileName_3230_);
lean_ctor_set(v___x_3247_, 1, v_fileMap_3231_);
lean_ctor_set(v___x_3247_, 2, v_options_3232_);
lean_ctor_set(v___x_3247_, 3, v_currRecDepth_3233_);
lean_ctor_set(v___x_3247_, 4, v_maxRecDepth_3234_);
lean_ctor_set(v___x_3247_, 5, v_ref_3246_);
lean_ctor_set(v___x_3247_, 6, v_currNamespace_3236_);
lean_ctor_set(v___x_3247_, 7, v_openDecls_3237_);
lean_ctor_set(v___x_3247_, 8, v_initHeartbeats_3238_);
lean_ctor_set(v___x_3247_, 9, v_maxHeartbeats_3239_);
lean_ctor_set(v___x_3247_, 10, v_quotContext_3240_);
lean_ctor_set(v___x_3247_, 11, v_currMacroScope_3241_);
lean_ctor_set(v___x_3247_, 12, v_cancelTk_x3f_3243_);
lean_ctor_set(v___x_3247_, 13, v_inheritedTraceOptions_3245_);
lean_ctor_set_uint8(v___x_3247_, sizeof(void*)*14, v_diag_3242_);
lean_ctor_set_uint8(v___x_3247_, sizeof(void*)*14 + 1, v_suppressElabErrors_3244_);
v___x_3248_ = l_Lean_throwError___at___00Lean_Meta_getElimExprInfo_spec__1___redArg(v_msg_3224_, v___y_3225_, v___y_3226_, v___x_3247_, v___y_3228_);
lean_dec_ref_known(v___x_3247_, 14);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3249_, lean_object* v_msg_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3249_, v_msg_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v_ref_3249_);
return v_res_3256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3257_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
lean_ctor_set(v___x_3262_, 2, v___x_3261_);
lean_ctor_set(v___x_3262_, 3, v___x_3261_);
lean_ctor_set(v___x_3262_, 4, v___x_3260_);
lean_ctor_set(v___x_3262_, 5, v___x_3260_);
lean_ctor_set(v___x_3262_, 6, v___x_3260_);
lean_ctor_set(v___x_3262_, 7, v___x_3260_);
lean_ctor_set(v___x_3262_, 8, v___x_3260_);
lean_ctor_set(v___x_3262_, 9, v___x_3260_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_unsigned_to_nat(32u);
v___x_3264_ = lean_mk_empty_array_with_capacity(v___x_3263_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3266_ = ((size_t)5ULL);
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = lean_unsigned_to_nat(32u);
v___x_3269_ = lean_mk_empty_array_with_capacity(v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v___x_3269_);
lean_ctor_set(v___x_3271_, 2, v___x_3267_);
lean_ctor_set(v___x_3271_, 3, v___x_3267_);
lean_ctor_set_usize(v___x_3271_, 4, v___x_3266_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3272_ = lean_box(1);
v___x_3273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_3274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v___x_3273_);
lean_ctor_set(v___x_3275_, 2, v___x_3272_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
return v___x_3284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3287_ = l_Lean_stringToMessageData(v___x_3286_);
return v___x_3287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3297_, lean_object* v_declHint_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v_env_3302_; uint8_t v___x_3303_; 
v___x_3301_ = lean_st_ref_get(v___y_3299_);
v_env_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_ref(v_env_3302_);
lean_dec(v___x_3301_);
v___x_3303_ = l_Lean_Name_isAnonymous(v_declHint_3298_);
if (v___x_3303_ == 0)
{
uint8_t v_isExporting_3304_; 
v_isExporting_3304_ = lean_ctor_get_uint8(v_env_3302_, sizeof(void*)*8);
if (v_isExporting_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_dec_ref(v_env_3302_);
lean_dec(v_declHint_3298_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v_msg_3297_);
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
lean_inc_ref(v_env_3302_);
v___x_3306_ = l_Lean_Environment_setExporting(v_env_3302_, v___x_3303_);
lean_inc(v_declHint_3298_);
lean_inc_ref(v___x_3306_);
v___x_3307_ = l_Lean_Environment_contains(v___x_3306_, v_declHint_3298_, v_isExporting_3304_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec_ref(v___x_3306_);
lean_dec_ref(v_env_3302_);
lean_dec(v_declHint_3298_);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_msg_3297_);
return v___x_3308_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_c_3314_; lean_object* v___x_3315_; 
v___x_3309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3311_ = l_Lean_Options_empty;
v___x_3312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3306_);
lean_ctor_set(v___x_3312_, 1, v___x_3309_);
lean_ctor_set(v___x_3312_, 2, v___x_3310_);
lean_ctor_set(v___x_3312_, 3, v___x_3311_);
lean_inc(v_declHint_3298_);
v___x_3313_ = l_Lean_MessageData_ofConstName(v_declHint_3298_, v___x_3303_);
v_c_3314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3314_, 0, v___x_3312_);
lean_ctor_set(v_c_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3302_, v_declHint_3298_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec_ref(v_env_3302_);
lean_dec(v_declHint_3298_);
v___x_3316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v_c_3314_);
v___x_3318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = l_Lean_MessageData_note(v___x_3319_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_msg_3297_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
else
{
lean_object* v_val_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3358_; 
v_val_3323_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3325_ = v___x_3315_;
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_val_3323_);
lean_dec(v___x_3315_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3358_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_mod_3330_; uint8_t v___x_3331_; 
v___x_3327_ = lean_box(0);
v___x_3328_ = l_Lean_Environment_header(v_env_3302_);
lean_dec_ref(v_env_3302_);
v___x_3329_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3328_);
v_mod_3330_ = lean_array_get(v___x_3327_, v___x_3329_, v_val_3323_);
lean_dec(v_val_3323_);
lean_dec_ref(v___x_3329_);
v___x_3331_ = l_Lean_isPrivateName(v_declHint_3298_);
lean_dec(v_declHint_3298_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3332_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v_c_3314_);
v___x_3334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_MessageData_ofName(v_mod_3330_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_MessageData_note(v___x_3339_);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v_msg_3297_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3341_);
v___x_3343_ = v___x_3325_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3345_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v_c_3314_);
v___x_3347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_MessageData_ofName(v_mod_3330_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = l_Lean_MessageData_note(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_msg_3297_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3354_);
v___x_3356_ = v___x_3325_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3359_; 
lean_dec_ref(v_env_3302_);
lean_dec(v_declHint_3298_);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v_msg_3297_);
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3360_, lean_object* v_declHint_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3360_, v_declHint_3361_, v___y_3362_);
lean_dec(v___y_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_3365_, lean_object* v_declHint_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3382_; 
v___x_3372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3365_, v_declHint_3366_, v___y_3370_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3377_ = l_Lean_unknownIdentifierMessageTag;
v___x_3378_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v_a_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3383_, lean_object* v_declHint_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3383_, v_declHint_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_3391_, lean_object* v_msg_3392_, lean_object* v_declHint_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v_a_3400_; lean_object* v___x_3401_; 
v___x_3399_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6(v_msg_3392_, v_declHint_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3391_, v_a_3400_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_3402_, lean_object* v_msg_3403_, lean_object* v_declHint_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3402_, v_msg_3403_, v_declHint_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v_ref_3402_);
return v_res_3410_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3414_, lean_object* v_constName_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3421_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_3422_ = 0;
lean_inc(v_constName_3415_);
v___x_3423_ = l_Lean_MessageData_ofConstName(v_constName_3415_, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3421_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8_once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_addImplicitTargets_collect___closed__8);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3414_, v___x_3426_, v_constName_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3428_, lean_object* v_constName_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3428_, v_constName_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v_ref_3428_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(lean_object* v_constName_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_ref_3442_; lean_object* v___x_3443_; 
v_ref_3442_ = lean_ctor_get(v___y_3439_, 5);
v___x_3443_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3442_, v_constName_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg___boxed(lean_object* v_constName_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(lean_object* v_constName_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___x_3457_; lean_object* v_env_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3457_ = lean_st_ref_get(v___y_3455_);
v_env_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc_ref(v_env_3458_);
lean_dec(v___x_3457_);
v___x_3459_ = 0;
lean_inc(v_constName_3451_);
v___x_3460_ = l_Lean_Environment_find_x3f(v_env_3458_, v_constName_3451_, v___x_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
return v___x_3461_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec(v_constName_3451_);
v_val_3462_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3460_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v___x_3460_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 0);
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_val_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3___boxed(lean_object* v_constName_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_constName_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* v_elimName_3477_, uint8_t v_induction_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_box(0);
lean_inc(v_elimName_3477_);
v___x_3485_ = l_Lean_Meta_getElimInfo(v_elimName_3477_, v___x_3484_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
lean_inc(v_elimName_3477_);
v___x_3487_ = l_Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3(v_elimName_3477_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = lean_box(v_induction_3478_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3490_, 0, v_a_3486_);
lean_closure_set(v___f_3490_, 1, v___x_3489_);
lean_closure_set(v___f_3490_, 2, v_elimName_3477_);
v___x_3491_ = l_Lean_ConstantInfo_type(v_a_3488_);
lean_dec(v_a_3488_);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getElimExprInfo_spec__2___redArg(v___x_3491_, v___f_3490_, v___x_3492_, v___x_3492_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
return v___x_3493_;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3486_);
lean_dec(v_elimName_3477_);
v_a_3494_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3487_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3487_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_elimName_3477_);
v_a_3502_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3485_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3485_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* v_elimName_3510_, lean_object* v_induction_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
uint8_t v_induction_boxed_3517_; lean_object* v_res_3518_; 
v_induction_boxed_3517_ = lean_unbox(v_induction_3511_);
v_res_3518_ = l_Lean_Meta_mkCustomEliminator(v_elimName_3510_, v_induction_boxed_3517_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(lean_object* v_upperBound_3519_, lean_object* v___x_3520_, lean_object* v_xs_3521_, lean_object* v___x_3522_, lean_object* v_inst_3523_, lean_object* v_R_3524_, lean_object* v_a_3525_, lean_object* v_b_3526_, lean_object* v_c_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___redArg(v_upperBound_3519_, v___x_3520_, v_xs_3521_, v___x_3522_, v_a_3525_, v_b_3526_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* v_upperBound_3534_, lean_object* v___x_3535_, lean_object* v_xs_3536_, lean_object* v___x_3537_, lean_object* v_inst_3538_, lean_object* v_R_3539_, lean_object* v_a_3540_, lean_object* v_b_3541_, lean_object* v_c_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__1(v_upperBound_3534_, v___x_3535_, v_xs_3536_, v___x_3537_, v_inst_3538_, v_R_3539_, v_a_3540_, v_b_3541_, v_c_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___x_3537_);
lean_dec_ref(v_xs_3536_);
lean_dec_ref(v___x_3535_);
lean_dec(v_upperBound_3534_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(lean_object* v_upperBound_3549_, lean_object* v___x_3550_, lean_object* v___x_3551_, lean_object* v_xs_3552_, lean_object* v_inst_3553_, lean_object* v_R_3554_, lean_object* v_a_3555_, lean_object* v_b_3556_, lean_object* v_c_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___redArg(v_upperBound_3549_, v___x_3550_, v___x_3551_, v_xs_3552_, v_a_3555_, v_b_3556_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* v_upperBound_3564_, lean_object* v___x_3565_, lean_object* v___x_3566_, lean_object* v_xs_3567_, lean_object* v_inst_3568_, lean_object* v_R_3569_, lean_object* v_a_3570_, lean_object* v_b_3571_, lean_object* v_c_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkCustomEliminator_spec__2(v_upperBound_3564_, v___x_3565_, v___x_3566_, v_xs_3567_, v_inst_3568_, v_R_3569_, v_a_3570_, v_b_3571_, v_c_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v_xs_3567_);
lean_dec_ref(v___x_3566_);
lean_dec(v___x_3565_);
lean_dec(v_upperBound_3564_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(lean_object* v_00_u03b1_3579_, lean_object* v_constName_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___redArg(v_constName_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3___boxed(lean_object* v_00_u03b1_3587_, lean_object* v_constName_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3(v_00_u03b1_3587_, v_constName_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_3595_, lean_object* v_ref_3596_, lean_object* v_constName_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___redArg(v_ref_3596_, v_constName_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_ref_3605_, lean_object* v_constName_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4(v_00_u03b1_3604_, v_ref_3605_, v_constName_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v_ref_3605_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3613_, lean_object* v_ref_3614_, lean_object* v_msg_3615_, lean_object* v_declHint_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___redArg(v_ref_3614_, v_msg_3615_, v_declHint_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3623_, lean_object* v_ref_3624_, lean_object* v_msg_3625_, lean_object* v_declHint_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3623_, v_ref_3624_, v_msg_3625_, v_declHint_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v_ref_3624_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(lean_object* v_msg_3633_, lean_object* v_declHint_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3633_, v_declHint_3634_, v___y_3638_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3641_, lean_object* v_declHint_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7(v_msg_3641_, v_declHint_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_3649_, lean_object* v_ref_3650_, lean_object* v_msg_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___redArg(v_ref_3650_, v_msg_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3658_, lean_object* v_ref_3659_, lean_object* v_msg_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__7(v_00_u03b1_3658_, v_ref_3659_, v_msg_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v_ref_3659_);
return v_res_3666_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__0);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__1);
v___x_3673_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
lean_ctor_set(v___x_3673_, 2, v___x_3672_);
lean_ctor_set(v___x_3673_, 3, v___x_3672_);
lean_ctor_set(v___x_3673_, 4, v___x_3672_);
lean_ctor_set(v___x_3673_, 5, v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* v_ext_3674_, lean_object* v_b_3675_, uint8_t v_kind_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_currNamespace_3681_; lean_object* v___x_3682_; lean_object* v_env_3683_; lean_object* v_nextMacroScope_3684_; lean_object* v_ngen_3685_; lean_object* v_auxDeclNGen_3686_; lean_object* v_traceState_3687_; lean_object* v_messages_3688_; lean_object* v_infoState_3689_; lean_object* v_snapshotTasks_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3717_; 
v_currNamespace_3681_ = lean_ctor_get(v___y_3678_, 6);
v___x_3682_ = lean_st_ref_take(v___y_3679_);
v_env_3683_ = lean_ctor_get(v___x_3682_, 0);
v_nextMacroScope_3684_ = lean_ctor_get(v___x_3682_, 1);
v_ngen_3685_ = lean_ctor_get(v___x_3682_, 2);
v_auxDeclNGen_3686_ = lean_ctor_get(v___x_3682_, 3);
v_traceState_3687_ = lean_ctor_get(v___x_3682_, 4);
v_messages_3688_ = lean_ctor_get(v___x_3682_, 6);
v_infoState_3689_ = lean_ctor_get(v___x_3682_, 7);
v_snapshotTasks_3690_ = lean_ctor_get(v___x_3682_, 8);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; 
v_unused_3718_ = lean_ctor_get(v___x_3682_, 5);
lean_dec(v_unused_3718_);
v___x_3692_ = v___x_3682_;
v_isShared_3693_ = v_isSharedCheck_3717_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_snapshotTasks_3690_);
lean_inc(v_infoState_3689_);
lean_inc(v_messages_3688_);
lean_inc(v_traceState_3687_);
lean_inc(v_auxDeclNGen_3686_);
lean_inc(v_ngen_3685_);
lean_inc(v_nextMacroScope_3684_);
lean_inc(v_env_3683_);
lean_dec(v___x_3682_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3717_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
lean_inc(v_currNamespace_3681_);
v___x_3694_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3683_, v_ext_3674_, v_b_3675_, v_kind_3676_, v_currNamespace_3681_);
v___x_3695_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__2);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 5, v___x_3695_);
lean_ctor_set(v___x_3692_, 0, v___x_3694_);
v___x_3697_ = v___x_3692_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_nextMacroScope_3684_);
lean_ctor_set(v_reuseFailAlloc_3716_, 2, v_ngen_3685_);
lean_ctor_set(v_reuseFailAlloc_3716_, 3, v_auxDeclNGen_3686_);
lean_ctor_set(v_reuseFailAlloc_3716_, 4, v_traceState_3687_);
lean_ctor_set(v_reuseFailAlloc_3716_, 5, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3716_, 6, v_messages_3688_);
lean_ctor_set(v_reuseFailAlloc_3716_, 7, v_infoState_3689_);
lean_ctor_set(v_reuseFailAlloc_3716_, 8, v_snapshotTasks_3690_);
v___x_3697_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v_mctx_3700_; lean_object* v_zetaDeltaFVarIds_3701_; lean_object* v_postponed_3702_; lean_object* v_diag_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3714_; 
v___x_3698_ = lean_st_ref_set(v___y_3679_, v___x_3697_);
v___x_3699_ = lean_st_ref_take(v___y_3677_);
v_mctx_3700_ = lean_ctor_get(v___x_3699_, 0);
v_zetaDeltaFVarIds_3701_ = lean_ctor_get(v___x_3699_, 2);
v_postponed_3702_ = lean_ctor_get(v___x_3699_, 3);
v_diag_3703_ = lean_ctor_get(v___x_3699_, 4);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; 
v_unused_3715_ = lean_ctor_get(v___x_3699_, 1);
lean_dec(v_unused_3715_);
v___x_3705_ = v___x_3699_;
v_isShared_3706_ = v_isSharedCheck_3714_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_diag_3703_);
lean_inc(v_postponed_3702_);
lean_inc(v_zetaDeltaFVarIds_3701_);
lean_inc(v_mctx_3700_);
lean_dec(v___x_3699_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3714_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___closed__3);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v___x_3707_);
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_mctx_3700_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_zetaDeltaFVarIds_3701_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_postponed_3702_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_diag_3703_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = lean_st_ref_set(v___y_3677_, v___x_3709_);
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* v_ext_3719_, lean_object* v_b_3720_, lean_object* v_kind_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v_kind_boxed_3726_; lean_object* v_res_3727_; 
v_kind_boxed_3726_ = lean_unbox(v_kind_3721_);
v_res_3727_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3719_, v_b_3720_, v_kind_boxed_3726_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(lean_object* v_00_u03b1_3728_, lean_object* v_00_u03b2_3729_, lean_object* v_00_u03c3_3730_, lean_object* v_ext_3731_, lean_object* v_b_3732_, uint8_t v_kind_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v_ext_3731_, v_b_3732_, v_kind_3733_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_00_u03b2_3741_, lean_object* v_00_u03c3_3742_, lean_object* v_ext_3743_, lean_object* v_b_3744_, lean_object* v_kind_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v_kind_boxed_3751_; lean_object* v_res_3752_; 
v_kind_boxed_3751_ = lean_unbox(v_kind_3745_);
v_res_3752_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0(v_00_u03b1_3740_, v_00_u03b2_3741_, v_00_u03c3_3742_, v_ext_3743_, v_b_3744_, v_kind_boxed_3751_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* v_declName_3753_, uint8_t v_attrKind_3754_, uint8_t v_induction_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Meta_mkCustomEliminator(v_declName_3753_, v_induction_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = l_Lean_Meta_customEliminatorExt;
v___x_3764_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addCustomEliminator_spec__0___redArg(v___x_3763_, v_a_3762_, v_attrKind_3754_, v_a_3757_, v_a_3758_, v_a_3759_);
return v___x_3764_;
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_a_3765_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3761_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3761_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* v_declName_3773_, lean_object* v_attrKind_3774_, lean_object* v_induction_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
uint8_t v_attrKind_boxed_3781_; uint8_t v_induction_boxed_3782_; lean_object* v_res_3783_; 
v_attrKind_boxed_3781_ = lean_unbox(v_attrKind_3774_);
v_induction_boxed_3782_ = lean_unbox(v_induction_3775_);
v_res_3783_ = l_Lean_Meta_addCustomEliminator(v_declName_3773_, v_attrKind_boxed_3781_, v_induction_boxed_3782_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
return v_res_3783_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3790_; uint64_t v___x_3791_; 
v___x_3790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3794_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set_uint64(v___x_3794_, sizeof(void*)*1, v___x_3792_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3799_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
lean_ctor_set(v___x_3799_, 3, v___x_3798_);
lean_ctor_set(v___x_3799_, 4, v___x_3798_);
lean_ctor_set(v___x_3799_, 5, v___x_3798_);
return v___x_3799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
lean_ctor_set(v___x_3801_, 2, v___x_3800_);
lean_ctor_set(v___x_3801_, 3, v___x_3800_);
lean_ctor_set(v___x_3801_, 4, v___x_3800_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3802_, lean_object* v___x_3803_, lean_object* v_declName_3804_, lean_object* v_x_3805_, uint8_t v_attrKind_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3810_ = 1;
v___x_3811_ = 0;
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3814_ = lean_unsigned_to_nat(32u);
v___x_3815_ = lean_mk_empty_array_with_capacity(v___x_3814_);
v___x_3816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3817_ = ((size_t)5ULL);
lean_inc_n(v___x_3802_, 6);
v___x_3818_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3815_);
lean_ctor_set(v___x_3818_, 2, v___x_3802_);
lean_ctor_set(v___x_3818_, 3, v___x_3802_);
lean_ctor_set_usize(v___x_3818_, 4, v___x_3817_);
v___x_3819_ = lean_box(1);
lean_inc_ref(v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3813_);
lean_ctor_set(v___x_3820_, 1, v___x_3818_);
lean_ctor_set(v___x_3820_, 2, v___x_3819_);
v___x_3821_ = lean_mk_empty_array_with_capacity(v___x_3802_);
v___x_3822_ = lean_box(0);
lean_inc(v___x_3803_);
v___x_3823_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3823_, 0, v___x_3812_);
lean_ctor_set(v___x_3823_, 1, v___x_3803_);
lean_ctor_set(v___x_3823_, 2, v___x_3820_);
lean_ctor_set(v___x_3823_, 3, v___x_3821_);
lean_ctor_set(v___x_3823_, 4, v___x_3822_);
lean_ctor_set(v___x_3823_, 5, v___x_3802_);
lean_ctor_set(v___x_3823_, 6, v___x_3822_);
lean_ctor_set_uint8(v___x_3823_, sizeof(void*)*7, v___x_3811_);
lean_ctor_set_uint8(v___x_3823_, sizeof(void*)*7 + 1, v___x_3811_);
lean_ctor_set_uint8(v___x_3823_, sizeof(void*)*7 + 2, v___x_3811_);
lean_ctor_set_uint8(v___x_3823_, sizeof(void*)*7 + 3, v___x_3810_);
v___x_3824_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3802_);
lean_ctor_set(v___x_3824_, 1, v___x_3802_);
lean_ctor_set(v___x_3824_, 2, v___x_3802_);
lean_ctor_set(v___x_3824_, 3, v___x_3802_);
lean_ctor_set(v___x_3824_, 4, v___x_3813_);
lean_ctor_set(v___x_3824_, 5, v___x_3813_);
lean_ctor_set(v___x_3824_, 6, v___x_3813_);
lean_ctor_set(v___x_3824_, 7, v___x_3813_);
lean_ctor_set(v___x_3824_, 8, v___x_3813_);
lean_ctor_set(v___x_3824_, 9, v___x_3813_);
v___x_3825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3824_);
lean_ctor_set(v___x_3827_, 1, v___x_3825_);
lean_ctor_set(v___x_3827_, 2, v___x_3803_);
lean_ctor_set(v___x_3827_, 3, v___x_3818_);
lean_ctor_set(v___x_3827_, 4, v___x_3826_);
v___x_3828_ = lean_st_mk_ref(v___x_3827_);
v___x_3829_ = l_Lean_Meta_addCustomEliminator(v_declName_3804_, v_attrKind_3806_, v___x_3810_, v___x_3823_, v___x_3828_, v___y_3807_, v___y_3808_);
lean_dec_ref_known(v___x_3823_, 7);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3838_; 
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v___x_3829_, 0);
lean_dec(v_unused_3839_);
v___x_3831_ = v___x_3829_;
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
else
{
lean_dec(v___x_3829_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3833_ = lean_st_ref_get(v___x_3828_);
lean_dec(v___x_3828_);
lean_dec(v___x_3833_);
v___x_3834_ = lean_box(0);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3834_);
v___x_3836_ = v___x_3831_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
else
{
lean_dec(v___x_3828_);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v_declName_3842_, lean_object* v_x_3843_, lean_object* v_attrKind_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
uint8_t v_attrKind_boxed_3848_; lean_object* v_res_3849_; 
v_attrKind_boxed_3848_ = lean_unbox(v_attrKind_3844_);
v_res_3849_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3840_, v___x_3841_, v_declName_3842_, v_x_3843_, v_attrKind_boxed_3848_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v_x_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; lean_object* v_env_3855_; lean_object* v_options_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3854_ = lean_st_ref_get(v___y_3852_);
v_env_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc_ref(v_env_3855_);
lean_dec(v___x_3854_);
v_options_3856_ = lean_ctor_get(v___y_3851_, 2);
v___x_3857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_3858_ = lean_unsigned_to_nat(32u);
v___x_3859_ = lean_mk_empty_array_with_capacity(v___x_3858_);
lean_dec_ref(v___x_3859_);
v___x_3860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
lean_inc_ref(v_options_3856_);
v___x_3861_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3861_, 0, v_env_3855_);
lean_ctor_set(v___x_3861_, 1, v___x_3857_);
lean_ctor_set(v___x_3861_, 2, v___x_3860_);
lean_ctor_set(v___x_3861_, 3, v_options_3856_);
v___x_3862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
lean_ctor_set(v___x_3862_, 1, v_msgData_3850_);
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msgData_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_ref_3873_; lean_object* v___x_3874_; lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3883_; 
v_ref_3873_ = lean_ctor_get(v___y_3870_, 5);
v___x_3874_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0_spec__0(v_msg_3869_, v___y_3870_, v___y_3871_);
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
lean_inc(v_ref_3873_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v_ref_3873_);
lean_ctor_set(v___x_3879_, 1, v_a_3875_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 1);
lean_ctor_set(v___x_3877_, 0, v___x_3879_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3888_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3891_ = l_Lean_stringToMessageData(v___x_3890_);
return v___x_3891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3894_ = l_Lean_stringToMessageData(v___x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(lean_object* v___x_3895_, lean_object* v_decl_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3901_ = l_Lean_MessageData_ofName(v___x_3895_);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3902_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_3904_, v___y_3897_, v___y_3898_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v___x_3906_, lean_object* v_decl_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(v___x_3906_, v_decl_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v_decl_3907_);
return v_res_3911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_unsigned_to_nat(2729305610u);
v___x_3963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3964_ = l_Lean_Name_num___override(v___x_3963_, v___x_3962_);
return v___x_3964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3968_ = l_Lean_Name_str___override(v___x_3967_, v___x_3966_);
return v___x_3968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3972_ = l_Lean_Name_str___override(v___x_3971_, v___x_3970_);
return v___x_3972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3973_ = lean_unsigned_to_nat(2u);
v___x_3974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3975_ = l_Lean_Name_num___override(v___x_3974_, v___x_3973_);
return v___x_3975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3982_ = 0;
v___x_3983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__29_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v___x_3984_);
lean_ctor_set(v___x_3986_, 2, v___x_3983_);
lean_ctor_set_uint8(v___x_3986_, sizeof(void*)*3, v___x_3982_);
return v___x_3986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___f_3987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___f_3988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_3989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__30_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
lean_ctor_set(v___x_3990_, 1, v___f_3988_);
lean_ctor_set(v___x_3990_, 2, v___f_3987_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__31_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_3993_ = l_Lean_registerBuiltinAttribute(v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3996_, lean_object* v_msg_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v_msg_3997_, v___y_3998_, v___y_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_4002_, lean_object* v_msg_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0(v_00_u03b1_4002_, v_msg_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_));
v___x_4012_ = l_Lean_addBuiltinDocString(v___x_4010_, v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2____boxed(lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_();
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v_declName_4017_, lean_object* v_x_4018_, uint8_t v_attrKind_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
uint8_t v___x_4023_; uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; size_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4023_ = 0;
v___x_4024_ = 1;
v___x_4025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4027_ = lean_unsigned_to_nat(32u);
v___x_4028_ = lean_mk_empty_array_with_capacity(v___x_4027_);
v___x_4029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkCustomEliminator_spec__3_spec__3_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_4030_ = ((size_t)5ULL);
lean_inc_n(v___x_4015_, 6);
v___x_4031_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4028_);
lean_ctor_set(v___x_4031_, 2, v___x_4015_);
lean_ctor_set(v___x_4031_, 3, v___x_4015_);
lean_ctor_set_usize(v___x_4031_, 4, v___x_4030_);
v___x_4032_ = lean_box(1);
lean_inc_ref(v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4026_);
lean_ctor_set(v___x_4033_, 1, v___x_4031_);
lean_ctor_set(v___x_4033_, 2, v___x_4032_);
v___x_4034_ = lean_mk_empty_array_with_capacity(v___x_4015_);
v___x_4035_ = lean_box(0);
lean_inc(v___x_4016_);
v___x_4036_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4036_, 0, v___x_4025_);
lean_ctor_set(v___x_4036_, 1, v___x_4016_);
lean_ctor_set(v___x_4036_, 2, v___x_4033_);
lean_ctor_set(v___x_4036_, 3, v___x_4034_);
lean_ctor_set(v___x_4036_, 4, v___x_4035_);
lean_ctor_set(v___x_4036_, 5, v___x_4015_);
lean_ctor_set(v___x_4036_, 6, v___x_4035_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*7, v___x_4023_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*7 + 1, v___x_4023_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*7 + 2, v___x_4023_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*7 + 3, v___x_4024_);
v___x_4037_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4015_);
lean_ctor_set(v___x_4037_, 1, v___x_4015_);
lean_ctor_set(v___x_4037_, 2, v___x_4015_);
lean_ctor_set(v___x_4037_, 3, v___x_4015_);
lean_ctor_set(v___x_4037_, 4, v___x_4026_);
lean_ctor_set(v___x_4037_, 5, v___x_4026_);
lean_ctor_set(v___x_4037_, 6, v___x_4026_);
lean_ctor_set(v___x_4037_, 7, v___x_4026_);
lean_ctor_set(v___x_4037_, 8, v___x_4026_);
lean_ctor_set(v___x_4037_, 9, v___x_4026_);
v___x_4038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4037_);
lean_ctor_set(v___x_4040_, 1, v___x_4038_);
lean_ctor_set(v___x_4040_, 2, v___x_4016_);
lean_ctor_set(v___x_4040_, 3, v___x_4031_);
lean_ctor_set(v___x_4040_, 4, v___x_4039_);
v___x_4041_ = lean_st_mk_ref(v___x_4040_);
v___x_4042_ = l_Lean_Meta_addCustomEliminator(v_declName_4017_, v_attrKind_4019_, v___x_4023_, v___x_4036_, v___x_4041_, v___y_4020_, v___y_4021_);
lean_dec_ref_known(v___x_4036_, 7);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4051_; 
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; 
v_unused_4052_ = lean_ctor_get(v___x_4042_, 0);
lean_dec(v_unused_4052_);
v___x_4044_ = v___x_4042_;
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v___x_4042_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4049_; 
v___x_4046_ = lean_st_ref_get(v___x_4041_);
lean_dec(v___x_4041_);
lean_dec(v___x_4046_);
v___x_4047_ = lean_box(0);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v___x_4047_);
v___x_4049_ = v___x_4044_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
else
{
lean_dec(v___x_4041_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4053_, lean_object* v___x_4054_, lean_object* v_declName_4055_, lean_object* v_x_4056_, lean_object* v_attrKind_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v_attrKind_boxed_4061_; lean_object* v_res_4062_; 
v_attrKind_boxed_4061_ = lean_unbox(v_attrKind_4057_);
v_res_4062_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4053_, v___x_4054_, v_declName_4055_, v_x_4056_, v_attrKind_boxed_4061_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v_x_4056_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(lean_object* v___x_4063_, lean_object* v_decl_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4069_ = l_Lean_MessageData_ofName(v___x_4063_);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2_);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_2729305610____hygCtx___hyg_2__spec__0___redArg(v___x_4072_, v___y_4065_, v___y_4066_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v___x_4074_, lean_object* v_decl_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(v___x_4074_, v_decl_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v_decl_4075_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4112_ = l_Lean_registerBuiltinAttribute(v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_));
v___x_4119_ = l_Lean_addBuiltinDocString(v___x_4117_, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2____boxed(lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Tactic_ElimInfo_913872705____hygCtx___hyg_2_();
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v_env_4125_; lean_object* v___x_4126_; lean_object* v_ext_4127_; lean_object* v_toEnvExtension_4128_; lean_object* v_asyncMode_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4124_ = lean_st_ref_get(v_a_4122_);
v_env_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc_ref(v_env_4125_);
lean_dec(v___x_4124_);
v___x_4126_ = l_Lean_Meta_customEliminatorExt;
v_ext_4127_ = lean_ctor_get(v___x_4126_, 1);
v_toEnvExtension_4128_ = lean_ctor_get(v_ext_4127_, 0);
v_asyncMode_4129_ = lean_ctor_get(v_toEnvExtension_4128_, 2);
v___x_4130_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4131_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4130_, v___x_4126_, v_env_4125_, v_asyncMode_4129_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4133_);
lean_dec(v_a_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_Meta_getCustomEliminators___redArg(v_a_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Meta_getCustomEliminators(v_a_4140_, v_a_4141_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_a_4144_, lean_object* v_x_4145_){
_start:
{
if (lean_obj_tag(v_x_4145_) == 0)
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_box(0);
return v___x_4146_;
}
else
{
lean_object* v_key_4147_; lean_object* v_value_4148_; lean_object* v_tail_4149_; lean_object* v_fst_4150_; lean_object* v_snd_4151_; lean_object* v_fst_4152_; lean_object* v_snd_4153_; uint8_t v___x_4162_; 
v_key_4147_ = lean_ctor_get(v_x_4145_, 0);
v_value_4148_ = lean_ctor_get(v_x_4145_, 1);
v_tail_4149_ = lean_ctor_get(v_x_4145_, 2);
v_fst_4150_ = lean_ctor_get(v_key_4147_, 0);
v_snd_4151_ = lean_ctor_get(v_key_4147_, 1);
v_fst_4152_ = lean_ctor_get(v_a_4144_, 0);
v_snd_4153_ = lean_ctor_get(v_a_4144_, 1);
v___x_4162_ = lean_unbox(v_fst_4150_);
if (v___x_4162_ == 0)
{
uint8_t v___x_4163_; 
v___x_4163_ = lean_unbox(v_fst_4152_);
if (v___x_4163_ == 0)
{
goto v___jp_4154_;
}
else
{
v_x_4145_ = v_tail_4149_;
goto _start;
}
}
else
{
uint8_t v___x_4165_; 
v___x_4165_ = lean_unbox(v_fst_4152_);
if (v___x_4165_ == 0)
{
v_x_4145_ = v_tail_4149_;
goto _start;
}
else
{
goto v___jp_4154_;
}
}
v___jp_4154_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4155_ = lean_array_get_size(v_snd_4151_);
v___x_4156_ = lean_array_get_size(v_snd_4153_);
v___x_4157_ = lean_nat_dec_eq(v___x_4155_, v___x_4156_);
if (v___x_4157_ == 0)
{
v_x_4145_ = v_tail_4149_;
goto _start;
}
else
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4151_, v_snd_4153_, v___x_4155_);
if (v___x_4159_ == 0)
{
v_x_4145_ = v_tail_4149_;
goto _start;
}
else
{
lean_object* v___x_4161_; 
lean_inc(v_value_4148_);
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v_value_4148_);
return v___x_4161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_4167_, lean_object* v_x_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4167_, v_x_4168_);
lean_dec(v_x_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(lean_object* v_m_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_buckets_4172_; lean_object* v_fst_4173_; lean_object* v_snd_4174_; lean_object* v___x_4175_; uint64_t v___y_4177_; uint64_t v___y_4178_; uint64_t v___y_4194_; uint8_t v___x_4206_; 
v_buckets_4172_ = lean_ctor_get(v_m_4170_, 1);
v_fst_4173_ = lean_ctor_get(v_a_4171_, 0);
v_snd_4174_ = lean_ctor_get(v_a_4171_, 1);
v___x_4175_ = lean_array_get_size(v_buckets_4172_);
v___x_4206_ = lean_unbox(v_fst_4173_);
if (v___x_4206_ == 0)
{
uint64_t v___x_4207_; 
v___x_4207_ = 13ULL;
v___y_4194_ = v___x_4207_;
goto v___jp_4193_;
}
else
{
uint64_t v___x_4208_; 
v___x_4208_ = 11ULL;
v___y_4194_ = v___x_4208_;
goto v___jp_4193_;
}
v___jp_4176_:
{
uint64_t v___x_4179_; uint64_t v___x_4180_; uint64_t v___x_4181_; uint64_t v_fold_4182_; uint64_t v___x_4183_; uint64_t v___x_4184_; uint64_t v___x_4185_; size_t v___x_4186_; size_t v___x_4187_; size_t v___x_4188_; size_t v___x_4189_; size_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4179_ = lean_uint64_mix_hash(v___y_4177_, v___y_4178_);
v___x_4180_ = 32ULL;
v___x_4181_ = lean_uint64_shift_right(v___x_4179_, v___x_4180_);
v_fold_4182_ = lean_uint64_xor(v___x_4179_, v___x_4181_);
v___x_4183_ = 16ULL;
v___x_4184_ = lean_uint64_shift_right(v_fold_4182_, v___x_4183_);
v___x_4185_ = lean_uint64_xor(v_fold_4182_, v___x_4184_);
v___x_4186_ = lean_uint64_to_usize(v___x_4185_);
v___x_4187_ = lean_usize_of_nat(v___x_4175_);
v___x_4188_ = ((size_t)1ULL);
v___x_4189_ = lean_usize_sub(v___x_4187_, v___x_4188_);
v___x_4190_ = lean_usize_land(v___x_4186_, v___x_4189_);
v___x_4191_ = lean_array_uget_borrowed(v_buckets_4172_, v___x_4190_);
v___x_4192_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4171_, v___x_4191_);
return v___x_4192_;
}
v___jp_4193_:
{
uint64_t v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4195_ = 7ULL;
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_array_get_size(v_snd_4174_);
v___x_4198_ = lean_nat_dec_lt(v___x_4196_, v___x_4197_);
if (v___x_4198_ == 0)
{
v___y_4177_ = v___y_4194_;
v___y_4178_ = v___x_4195_;
goto v___jp_4176_;
}
else
{
uint8_t v___x_4199_; 
v___x_4199_ = lean_nat_dec_le(v___x_4197_, v___x_4197_);
if (v___x_4199_ == 0)
{
if (v___x_4198_ == 0)
{
v___y_4177_ = v___y_4194_;
v___y_4178_ = v___x_4195_;
goto v___jp_4176_;
}
else
{
size_t v___x_4200_; size_t v___x_4201_; uint64_t v___x_4202_; 
v___x_4200_ = ((size_t)0ULL);
v___x_4201_ = lean_usize_of_nat(v___x_4197_);
v___x_4202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4174_, v___x_4200_, v___x_4201_, v___x_4195_);
v___y_4177_ = v___y_4194_;
v___y_4178_ = v___x_4202_;
goto v___jp_4176_;
}
}
else
{
size_t v___x_4203_; size_t v___x_4204_; uint64_t v___x_4205_; 
v___x_4203_ = ((size_t)0ULL);
v___x_4204_ = lean_usize_of_nat(v___x_4197_);
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4174_, v___x_4203_, v___x_4204_, v___x_4195_);
v___y_4177_ = v___y_4194_;
v___y_4178_ = v___x_4205_;
goto v___jp_4176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_m_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4209_, v_a_4210_);
lean_dec_ref(v_a_4210_);
lean_dec_ref(v_m_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_4212_, lean_object* v_vals_4213_, lean_object* v_i_4214_, lean_object* v_k_4215_){
_start:
{
lean_object* v___x_4220_; uint8_t v___x_4221_; 
v___x_4220_ = lean_array_get_size(v_keys_4212_);
v___x_4221_ = lean_nat_dec_lt(v_i_4214_, v___x_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; 
lean_dec(v_i_4214_);
v___x_4222_ = lean_box(0);
return v___x_4222_;
}
else
{
lean_object* v_fst_4223_; lean_object* v_snd_4224_; lean_object* v_k_x27_4225_; lean_object* v_fst_4226_; lean_object* v_snd_4227_; uint8_t v___y_4229_; uint8_t v___x_4236_; 
v_fst_4223_ = lean_ctor_get(v_k_4215_, 0);
v_snd_4224_ = lean_ctor_get(v_k_4215_, 1);
v_k_x27_4225_ = lean_array_fget_borrowed(v_keys_4212_, v_i_4214_);
v_fst_4226_ = lean_ctor_get(v_k_x27_4225_, 0);
v_snd_4227_ = lean_ctor_get(v_k_x27_4225_, 1);
v___x_4236_ = lean_unbox(v_fst_4223_);
if (v___x_4236_ == 0)
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_unbox(v_fst_4226_);
if (v___x_4237_ == 0)
{
v___y_4229_ = v___x_4221_;
goto v___jp_4228_;
}
else
{
goto v___jp_4216_;
}
}
else
{
uint8_t v___x_4238_; 
v___x_4238_ = lean_unbox(v_fst_4226_);
v___y_4229_ = v___x_4238_;
goto v___jp_4228_;
}
v___jp_4228_:
{
if (v___y_4229_ == 0)
{
goto v___jp_4216_;
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v___x_4230_ = lean_array_get_size(v_snd_4224_);
v___x_4231_ = lean_array_get_size(v_snd_4227_);
v___x_4232_ = lean_nat_dec_eq(v___x_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
goto v___jp_4216_;
}
else
{
uint8_t v___x_4233_; 
v___x_4233_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4224_, v_snd_4227_, v___x_4230_);
if (v___x_4233_ == 0)
{
goto v___jp_4216_;
}
else
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = lean_array_fget_borrowed(v_vals_4213_, v_i_4214_);
lean_dec(v_i_4214_);
lean_inc(v___x_4234_);
v___x_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
}
}
}
}
v___jp_4216_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_unsigned_to_nat(1u);
v___x_4218_ = lean_nat_add(v_i_4214_, v___x_4217_);
lean_dec(v_i_4214_);
v_i_4214_ = v___x_4218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_4239_, lean_object* v_vals_4240_, lean_object* v_i_4241_, lean_object* v_k_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4239_, v_vals_4240_, v_i_4241_, v_k_4242_);
lean_dec_ref(v_k_4242_);
lean_dec_ref(v_vals_4240_);
lean_dec_ref(v_keys_4239_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_4244_, size_t v_x_4245_, lean_object* v_x_4246_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_object* v_es_4247_; lean_object* v___x_4248_; size_t v___x_4249_; size_t v___x_4250_; lean_object* v_j_4251_; lean_object* v___x_4252_; 
v_es_4247_ = lean_ctor_get(v_x_4244_, 0);
v___x_4248_ = lean_box(2);
v___x_4249_ = ((size_t)31ULL);
v___x_4250_ = lean_usize_land(v_x_4245_, v___x_4249_);
v_j_4251_ = lean_usize_to_nat(v___x_4250_);
v___x_4252_ = lean_array_get_borrowed(v___x_4248_, v_es_4247_, v_j_4251_);
lean_dec(v_j_4251_);
switch(lean_obj_tag(v___x_4252_))
{
case 0:
{
lean_object* v_key_4253_; lean_object* v_val_4254_; lean_object* v_fst_4255_; lean_object* v_snd_4256_; lean_object* v_fst_4257_; lean_object* v_snd_4258_; uint8_t v___x_4267_; 
v_key_4253_ = lean_ctor_get(v___x_4252_, 0);
v_val_4254_ = lean_ctor_get(v___x_4252_, 1);
v_fst_4255_ = lean_ctor_get(v_x_4246_, 0);
v_snd_4256_ = lean_ctor_get(v_x_4246_, 1);
v_fst_4257_ = lean_ctor_get(v_key_4253_, 0);
v_snd_4258_ = lean_ctor_get(v_key_4253_, 1);
v___x_4267_ = lean_unbox(v_fst_4255_);
if (v___x_4267_ == 0)
{
uint8_t v___x_4268_; 
v___x_4268_ = lean_unbox(v_fst_4257_);
if (v___x_4268_ == 0)
{
goto v___jp_4259_;
}
else
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_box(0);
return v___x_4269_;
}
}
else
{
uint8_t v___x_4270_; 
v___x_4270_ = lean_unbox(v_fst_4257_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_box(0);
return v___x_4271_;
}
else
{
goto v___jp_4259_;
}
}
v___jp_4259_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4260_ = lean_array_get_size(v_snd_4256_);
v___x_4261_ = lean_array_get_size(v_snd_4258_);
v___x_4262_ = lean_nat_dec_eq(v___x_4260_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_box(0);
return v___x_4263_;
}
else
{
uint8_t v___x_4264_; 
v___x_4264_ = l_Array_isEqvAux___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_snd_4256_, v_snd_4258_, v___x_4260_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_box(0);
return v___x_4265_;
}
else
{
lean_object* v___x_4266_; 
lean_inc(v_val_4254_);
v___x_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4266_, 0, v_val_4254_);
return v___x_4266_;
}
}
}
}
case 1:
{
lean_object* v_node_4272_; size_t v___x_4273_; size_t v___x_4274_; 
v_node_4272_ = lean_ctor_get(v___x_4252_, 0);
v___x_4273_ = ((size_t)5ULL);
v___x_4274_ = lean_usize_shift_right(v_x_4245_, v___x_4273_);
v_x_4244_ = v_node_4272_;
v_x_4245_ = v___x_4274_;
goto _start;
}
default: 
{
lean_object* v___x_4276_; 
v___x_4276_ = lean_box(0);
return v___x_4276_;
}
}
}
else
{
lean_object* v_ks_4277_; lean_object* v_vs_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v_ks_4277_ = lean_ctor_get(v_x_4244_, 0);
v_vs_4278_ = lean_ctor_get(v_x_4244_, 1);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_ks_4277_, v_vs_4278_, v___x_4279_, v_x_4246_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
size_t v_x_2269__boxed_4284_; lean_object* v_res_4285_; 
v_x_2269__boxed_4284_ = lean_unbox_usize(v_x_4282_);
lean_dec(v_x_4282_);
v_res_4285_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4281_, v_x_2269__boxed_4284_, v_x_4283_);
lean_dec_ref(v_x_4283_);
lean_dec_ref(v_x_4281_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* v_x_4286_, lean_object* v_x_4287_){
_start:
{
uint64_t v___y_4289_; uint64_t v___y_4290_; lean_object* v_fst_4294_; lean_object* v_snd_4295_; uint64_t v___y_4297_; uint8_t v___x_4309_; 
v_fst_4294_ = lean_ctor_get(v_x_4287_, 0);
v_snd_4295_ = lean_ctor_get(v_x_4287_, 1);
v___x_4309_ = lean_unbox(v_fst_4294_);
if (v___x_4309_ == 0)
{
uint64_t v___x_4310_; 
v___x_4310_ = 13ULL;
v___y_4297_ = v___x_4310_;
goto v___jp_4296_;
}
else
{
uint64_t v___x_4311_; 
v___x_4311_ = 11ULL;
v___y_4297_ = v___x_4311_;
goto v___jp_4296_;
}
v___jp_4288_:
{
uint64_t v___x_4291_; size_t v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_uint64_mix_hash(v___y_4289_, v___y_4290_);
v___x_4292_ = lean_uint64_to_usize(v___x_4291_);
v___x_4293_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4286_, v___x_4292_, v_x_4287_);
return v___x_4293_;
}
v___jp_4296_:
{
uint64_t v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4298_ = 7ULL;
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = lean_array_get_size(v_snd_4295_);
v___x_4301_ = lean_nat_dec_lt(v___x_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
v___y_4289_ = v___y_4297_;
v___y_4290_ = v___x_4298_;
goto v___jp_4288_;
}
else
{
uint8_t v___x_4302_; 
v___x_4302_ = lean_nat_dec_le(v___x_4300_, v___x_4300_);
if (v___x_4302_ == 0)
{
if (v___x_4301_ == 0)
{
v___y_4289_ = v___y_4297_;
v___y_4290_ = v___x_4298_;
goto v___jp_4288_;
}
else
{
size_t v___x_4303_; size_t v___x_4304_; uint64_t v___x_4305_; 
v___x_4303_ = ((size_t)0ULL);
v___x_4304_ = lean_usize_of_nat(v___x_4300_);
v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4295_, v___x_4303_, v___x_4304_, v___x_4298_);
v___y_4289_ = v___y_4297_;
v___y_4290_ = v___x_4305_;
goto v___jp_4288_;
}
}
else
{
size_t v___x_4306_; size_t v___x_4307_; uint64_t v___x_4308_; 
v___x_4306_ = ((size_t)0ULL);
v___x_4307_ = lean_usize_of_nat(v___x_4300_);
v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__2(v_snd_4295_, v___x_4306_, v___x_4307_, v___x_4298_);
v___y_4289_ = v___y_4297_;
v___y_4290_ = v___x_4308_;
goto v___jp_4288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_4312_, lean_object* v_x_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4312_, v_x_4313_);
lean_dec_ref(v_x_4313_);
lean_dec_ref(v_x_4312_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
uint8_t v_stage_u2081_4317_; 
v_stage_u2081_4317_ = lean_ctor_get_uint8(v_x_4315_, sizeof(void*)*2);
if (v_stage_u2081_4317_ == 0)
{
lean_object* v_map_u2081_4318_; lean_object* v_map_u2082_4319_; lean_object* v___x_4320_; 
v_map_u2081_4318_ = lean_ctor_get(v_x_4315_, 0);
v_map_u2082_4319_ = lean_ctor_get(v_x_4315_, 1);
v___x_4320_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_map_u2082_4319_, v_x_4316_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4318_, v_x_4316_);
return v___x_4321_;
}
else
{
return v___x_4320_;
}
}
else
{
lean_object* v_map_u2081_4322_; lean_object* v___x_4323_; 
v_map_u2081_4322_ = lean_ctor_get(v_x_4315_, 0);
v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_map_u2081_4322_, v_x_4316_);
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg___boxed(lean_object* v_x_4324_, lean_object* v_x_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4324_, v_x_4325_);
lean_dec_ref(v_x_4325_);
lean_dec_ref(v_x_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* v_as_4329_, size_t v_sz_4330_, size_t v_i_4331_, lean_object* v_b_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
uint8_t v___x_4338_; 
v___x_4338_ = lean_usize_dec_lt(v_i_4331_, v_sz_4330_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v_b_4332_);
return v___x_4339_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4341_; 
v_a_4340_ = lean_array_uget_borrowed(v_as_4329_, v_i_4331_);
lean_inc(v___y_4336_);
lean_inc_ref(v___y_4335_);
lean_inc(v___y_4334_);
lean_inc_ref(v___y_4333_);
lean_inc(v_a_4340_);
v___x_4341_ = lean_infer_type(v_a_4340_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4343_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4341_, 1);
v___x_4343_ = l_Lean_instantiateMVars___at___00Lean_Meta_addImplicitTargets_spec__2___redArg(v_a_4342_, v___y_4334_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4372_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4346_ = v___x_4343_;
v_isShared_4347_ = v_isSharedCheck_4372_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4343_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4372_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v_snd_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4370_; 
v_snd_4348_ = lean_ctor_get(v_b_4332_, 1);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_b_4332_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v_b_4332_, 0);
lean_dec(v_unused_4371_);
v___x_4350_ = v_b_4332_;
v_isShared_4351_ = v_isSharedCheck_4370_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_snd_4348_);
lean_dec(v_b_4332_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4370_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = l_Lean_Expr_headBeta(v_a_4344_);
v___x_4353_ = l_Lean_Expr_getAppFn(v___x_4352_);
lean_dec_ref(v___x_4352_);
if (lean_obj_tag(v___x_4353_) == 4)
{
lean_object* v_declName_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_del_object(v___x_4346_);
v_declName_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_declName_4354_);
lean_dec_ref_known(v___x_4353_, 2);
v___x_4355_ = lean_box(0);
v___x_4356_ = lean_array_push(v_snd_4348_, v_declName_4354_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 1, v___x_4356_);
lean_ctor_set(v___x_4350_, 0, v___x_4355_);
v___x_4358_ = v___x_4350_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v___x_4356_);
v___x_4358_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
size_t v___x_4359_; size_t v___x_4360_; 
v___x_4359_ = ((size_t)1ULL);
v___x_4360_ = lean_usize_add(v_i_4331_, v___x_4359_);
v_i_4331_ = v___x_4360_;
v_b_4332_ = v___x_4358_;
goto _start;
}
}
else
{
lean_object* v___x_4363_; lean_object* v___x_4365_; 
lean_dec_ref(v___x_4353_);
v___x_4363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___closed__0));
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4363_);
v___x_4365_ = v___x_4350_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_snd_4348_);
v___x_4365_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4367_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4365_);
v___x_4367_ = v___x_4346_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec_ref(v_b_4332_);
v_a_4373_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4343_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4343_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v_b_4332_);
v_a_4381_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4341_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4341_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* v_as_4389_, lean_object* v_sz_4390_, lean_object* v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
size_t v_sz_boxed_4398_; size_t v_i_boxed_4399_; lean_object* v_res_4400_; 
v_sz_boxed_4398_ = lean_unbox_usize(v_sz_4390_);
lean_dec(v_sz_4390_);
v_i_boxed_4399_ = lean_unbox_usize(v_i_4391_);
lean_dec(v_i_4391_);
v_res_4400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_as_4389_, v_sz_boxed_4398_, v_i_boxed_4399_, v_b_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec_ref(v_as_4389_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* v_targets_4404_, uint8_t v_induction_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v___x_4411_; size_t v_sz_4412_; size_t v___x_4413_; lean_object* v___x_4414_; 
v___x_4411_ = ((lean_object*)(l_Lean_Meta_getCustomEliminator_x3f___closed__0));
v_sz_4412_ = lean_array_size(v_targets_4404_);
v___x_4413_ = ((size_t)0ULL);
v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_getCustomEliminator_x3f_spec__0(v_targets_4404_, v_sz_4412_, v___x_4413_, v___x_4411_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4446_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4446_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4446_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v_fst_4419_; 
v_fst_4419_ = lean_ctor_get(v_a_4415_, 0);
if (lean_obj_tag(v_fst_4419_) == 0)
{
lean_object* v_snd_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4440_; 
v_snd_4420_ = lean_ctor_get(v_a_4415_, 1);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_a_4415_);
if (v_isSharedCheck_4440_ == 0)
{
lean_object* v_unused_4441_; 
v_unused_4441_ = lean_ctor_get(v_a_4415_, 0);
lean_dec(v_unused_4441_);
v___x_4422_ = v_a_4415_;
v_isShared_4423_ = v_isSharedCheck_4440_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_snd_4420_);
lean_dec(v_a_4415_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4440_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v_env_4425_; lean_object* v___x_4426_; lean_object* v_ext_4427_; lean_object* v_toEnvExtension_4428_; lean_object* v_asyncMode_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4424_ = lean_st_ref_get(v_a_4409_);
v_env_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc_ref(v_env_4425_);
lean_dec(v___x_4424_);
v___x_4426_ = l_Lean_Meta_customEliminatorExt;
v_ext_4427_ = lean_ctor_get(v___x_4426_, 1);
v_toEnvExtension_4428_ = lean_ctor_get(v_ext_4427_, 0);
v_asyncMode_4429_ = lean_ctor_get(v_toEnvExtension_4428_, 2);
v___x_4430_ = l_Lean_Meta_instInhabitedCustomEliminators_default;
v___x_4431_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4430_, v___x_4426_, v_env_4425_, v_asyncMode_4429_);
v___x_4432_ = lean_box(v_induction_4405_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4432_);
v___x_4434_ = v___x_4422_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_snd_4420_);
v___x_4434_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v___x_4431_, v___x_4434_);
lean_dec_ref(v___x_4434_);
lean_dec(v___x_4431_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4435_);
v___x_4437_ = v___x_4417_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
else
{
lean_object* v_val_4442_; lean_object* v___x_4444_; 
lean_inc_ref(v_fst_4419_);
lean_dec(v_a_4415_);
v_val_4442_ = lean_ctor_get(v_fst_4419_, 0);
lean_inc(v_val_4442_);
lean_dec_ref_known(v_fst_4419_, 1);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v_val_4442_);
v___x_4444_ = v___x_4417_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_val_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_a_4447_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4414_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4414_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* v_targets_4455_, lean_object* v_induction_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
uint8_t v_induction_boxed_4462_; lean_object* v_res_4463_; 
v_induction_boxed_4462_ = lean_unbox(v_induction_4456_);
v_res_4463_ = l_Lean_Meta_getCustomEliminator_x3f(v_targets_4455_, v_induction_boxed_4462_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec_ref(v_targets_4455_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* v_00_u03b2_4464_, lean_object* v_x_4465_, lean_object* v_x_4466_){
_start:
{
lean_object* v___x_4467_; 
v___x_4467_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(v_x_4465_, v_x_4466_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1___boxed(lean_object* v_00_u03b2_4468_, lean_object* v_x_4469_, lean_object* v_x_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1(v_00_u03b2_4468_, v_x_4469_, v_x_4470_);
lean_dec_ref(v_x_4470_);
lean_dec_ref(v_x_4469_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* v_00_u03b2_4472_, lean_object* v_x_4473_, lean_object* v_x_4474_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(v_x_4473_, v_x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4476_, lean_object* v_x_4477_, lean_object* v_x_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(v_00_u03b2_4476_, v_x_4477_, v_x_4478_);
lean_dec_ref(v_x_4478_);
lean_dec_ref(v_x_4477_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(lean_object* v_00_u03b2_4480_, lean_object* v_m_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___redArg(v_m_4481_, v_a_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4484_, lean_object* v_m_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2(v_00_u03b2_4484_, v_m_4485_, v_a_4486_);
lean_dec_ref(v_a_4486_);
lean_dec_ref(v_m_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4488_, lean_object* v_x_4489_, size_t v_x_4490_, lean_object* v_x_4491_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___redArg(v_x_4489_, v_x_4490_, v_x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_){
_start:
{
size_t v_x_2641__boxed_4497_; lean_object* v_res_4498_; 
v_x_2641__boxed_4497_ = lean_unbox_usize(v_x_4495_);
lean_dec(v_x_4495_);
v_res_4498_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2(v_00_u03b2_4493_, v_x_4494_, v_x_2641__boxed_4497_, v_x_4496_);
lean_dec_ref(v_x_4496_);
lean_dec_ref(v_x_4494_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4499_, lean_object* v_a_4500_, lean_object* v_x_4501_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___redArg(v_a_4500_, v_x_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4503_, lean_object* v_a_4504_, lean_object* v_x_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__2_spec__4(v_00_u03b2_4503_, v_a_4504_, v_x_4505_);
lean_dec(v_x_4505_);
lean_dec_ref(v_a_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4507_, lean_object* v_keys_4508_, lean_object* v_vals_4509_, lean_object* v_heq_4510_, lean_object* v_i_4511_, lean_object* v_k_4512_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_keys_4508_, v_vals_4509_, v_i_4511_, v_k_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4514_, lean_object* v_keys_4515_, lean_object* v_vals_4516_, lean_object* v_heq_4517_, lean_object* v_i_4518_, lean_object* v_k_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_4514_, v_keys_4515_, v_vals_4516_, v_heq_4517_, v_i_4518_, v_k_4519_);
lean_dec_ref(v_k_4519_);
lean_dec_ref(v_vals_4516_);
lean_dec_ref(v_keys_4515_);
return v_res_4520_;
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

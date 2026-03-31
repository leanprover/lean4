// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Cases
// Imports: public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Grind.Extension
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_NameSet_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedCasesEntry = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Empty"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid `[grind cases]`, `"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__1;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` is not an inductive datatype or an alias for one"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__3;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid `[grind cases eager]`, `"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__5;
static const lean_string_object l_Lean_Meta_Grind_validateCasesAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` is not a non-recursive inductive datatype or an alias for one"};
static const lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_validateCasesAttr___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_validateCasesAttr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_validateCasesAttr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1;
static const lean_string_object l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "` is marked as a built-in case-split for `grind` and cannot be erased"};
static const lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(168, 230, 231, 67, 23, 65, 31, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "(non-recursive) inductive type expected at "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unexpected recursor type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_cases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_cases___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_cases___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_cases___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Grind_cases___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_cases___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17));
v___x_43_ = l_Lean_NameSet_ofList(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18);
return v___x_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object* v_declName_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
v___x_47_ = l_Lean_NameSet_contains(v___x_46_, v_declName_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(lean_object* v_declName_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_48_);
lean_dec(v_declName_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_51_, lean_object* v_i_52_, lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_keys_51_);
v___x_55_ = lean_nat_dec_lt(v_i_52_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec(v_i_52_);
return v___x_55_;
}
else
{
lean_object* v_k_x27_56_; uint8_t v___x_57_; 
v_k_x27_56_ = lean_array_fget_borrowed(v_keys_51_, v_i_52_);
v___x_57_ = lean_name_eq(v_k_53_, v_k_x27_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_i_52_, v___x_58_);
lean_dec(v_i_52_);
v_i_52_ = v___x_59_;
goto _start;
}
else
{
lean_dec(v_i_52_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_61_, lean_object* v_i_62_, lean_object* v_k_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_61_, v_i_62_, v_k_63_);
lean_dec(v_k_63_);
lean_dec_ref(v_keys_61_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_66_; size_t v___x_67_; size_t v___x_68_; 
v___x_66_ = ((size_t)5ULL);
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_shift_left(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; 
v___x_69_ = ((size_t)1ULL);
v___x_70_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0);
v___x_71_ = lean_usize_sub(v___x_70_, v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object* v_x_72_, size_t v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_es_75_; lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_j_80_; lean_object* v___x_81_; 
v_es_75_ = lean_ctor_get(v_x_72_, 0);
v___x_76_ = lean_box(2);
v___x_77_ = ((size_t)5ULL);
v___x_78_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
v___x_79_ = lean_usize_land(v_x_73_, v___x_78_);
v_j_80_ = lean_usize_to_nat(v___x_79_);
v___x_81_ = lean_array_get_borrowed(v___x_76_, v_es_75_, v_j_80_);
lean_dec(v_j_80_);
switch(lean_obj_tag(v___x_81_))
{
case 0:
{
lean_object* v_key_82_; uint8_t v___x_83_; 
v_key_82_ = lean_ctor_get(v___x_81_, 0);
v___x_83_ = lean_name_eq(v_x_74_, v_key_82_);
return v___x_83_;
}
case 1:
{
lean_object* v_node_84_; size_t v___x_85_; 
v_node_84_ = lean_ctor_get(v___x_81_, 0);
v___x_85_ = lean_usize_shift_right(v_x_73_, v___x_77_);
v_x_72_ = v_node_84_;
v_x_73_ = v___x_85_;
goto _start;
}
default: 
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
}
else
{
lean_object* v_ks_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_ks_88_ = lean_ctor_get(v_x_72_, 0);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_ks_88_, v___x_89_, v_x_74_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
size_t v_x_139__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_x_139__boxed_94_ = lean_unbox_usize(v_x_92_);
lean_dec(v_x_92_);
v_res_95_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_91_, v_x_139__boxed_94_, v_x_93_);
lean_dec(v_x_93_);
lean_dec_ref(v_x_91_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_97_; uint64_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1723u);
v___x_98_ = lean_uint64_of_nat(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint64_t v___y_102_; 
if (lean_obj_tag(v_x_100_) == 0)
{
uint64_t v___x_105_; 
v___x_105_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
v___y_102_ = v___x_105_;
goto v___jp_101_;
}
else
{
uint64_t v_hash_106_; 
v_hash_106_ = lean_ctor_get_uint64(v_x_100_, sizeof(void*)*2);
v___y_102_ = v_hash_106_;
goto v___jp_101_;
}
v___jp_101_:
{
size_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_uint64_to_usize(v___y_102_);
v___x_104_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_99_, v___x_103_, v_x_100_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec_ref(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object* v_s_111_, lean_object* v_declName_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_111_, v_declName_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object* v_s_114_, lean_object* v_declName_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_114_, v_declName_115_);
lean_dec(v_declName_115_);
lean_dec_ref(v_s_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object* v_00_u03b2_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_119_, v_x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object* v_00_u03b2_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(v_00_u03b2_122_, v_x_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec_ref(v_x_123_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object* v_00_u03b2_127_, lean_object* v_x_128_, size_t v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_128_, v_x_129_, v_x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
size_t v_x_218__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_218__boxed_136_ = lean_unbox_usize(v_x_134_);
lean_dec(v_x_134_);
v_res_137_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(v_00_u03b2_132_, v_x_133_, v_x_218__boxed_136_, v_x_135_);
lean_dec(v_x_135_);
lean_dec_ref(v_x_133_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_139_, lean_object* v_keys_140_, lean_object* v_vals_141_, lean_object* v_heq_142_, lean_object* v_i_143_, lean_object* v_k_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_140_, v_i_143_, v_k_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_146_, lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_heq_149_, lean_object* v_i_150_, lean_object* v_k_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(v_00_u03b2_146_, v_keys_147_, v_vals_148_, v_heq_149_, v_i_150_, v_k_151_);
lean_dec(v_k_151_);
lean_dec_ref(v_vals_148_);
lean_dec_ref(v_keys_147_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_154_, lean_object* v_v_155_, lean_object* v_i_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_array_get_size(v_xs_154_);
v___x_158_ = lean_nat_dec_lt(v_i_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec(v_i_156_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_array_fget_borrowed(v_xs_154_, v_i_156_);
v___x_161_ = lean_name_eq(v___x_160_, v_v_155_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_i_156_, v___x_162_);
lean_dec(v_i_156_);
v_i_156_ = v___x_163_;
goto _start;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_i_156_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_166_, lean_object* v_v_167_, lean_object* v_i_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_166_, v_v_167_, v_i_168_);
lean_dec(v_v_167_);
lean_dec_ref(v_xs_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object* v_xs_170_, lean_object* v_v_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_170_, v_v_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_174_, lean_object* v_v_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_xs_174_, v_v_175_);
lean_dec(v_v_175_);
lean_dec_ref(v_xs_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object* v_x_177_, size_t v_x_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_es_180_; lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v_j_185_; lean_object* v_entry_186_; 
v_es_180_ = lean_ctor_get(v_x_177_, 0);
v___x_181_ = lean_box(2);
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
v___x_184_ = lean_usize_land(v_x_178_, v___x_183_);
v_j_185_ = lean_usize_to_nat(v___x_184_);
v_entry_186_ = lean_array_get(v___x_181_, v_es_180_, v_j_185_);
switch(lean_obj_tag(v_entry_186_))
{
case 0:
{
lean_object* v_key_187_; uint8_t v___x_188_; 
v_key_187_ = lean_ctor_get(v_entry_186_, 0);
lean_inc(v_key_187_);
lean_dec_ref(v_entry_186_);
v___x_188_ = lean_name_eq(v_x_179_, v_key_187_);
lean_dec(v_key_187_);
if (v___x_188_ == 0)
{
lean_dec(v_j_185_);
return v_x_177_;
}
else
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
lean_inc_ref(v_es_180_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v_x_177_, 0);
lean_dec(v_unused_197_);
v___x_190_ = v_x_177_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_x_177_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_array_set(v_es_180_, v_j_185_, v___x_181_);
lean_dec(v_j_185_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
case 1:
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_231_; 
lean_inc_ref(v_es_180_);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_x_177_, 0);
lean_dec(v_unused_232_);
v___x_199_ = v_x_177_;
v_isShared_200_ = v_isSharedCheck_231_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_x_177_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_231_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_node_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_230_; 
v_node_201_ = lean_ctor_get(v_entry_186_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_entry_186_);
if (v_isSharedCheck_230_ == 0)
{
v___x_203_ = v_entry_186_;
v_isShared_204_ = v_isSharedCheck_230_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_node_201_);
lean_dec(v_entry_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_230_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_entries_205_; size_t v___x_206_; lean_object* v_newNode_207_; lean_object* v___x_208_; 
v_entries_205_ = lean_array_set(v_es_180_, v_j_185_, v___x_181_);
v___x_206_ = lean_usize_shift_right(v_x_178_, v___x_182_);
v_newNode_207_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_node_201_, v___x_206_, v_x_179_);
lean_inc_ref(v_newNode_207_);
v___x_208_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v_newNode_207_);
v___x_210_ = v___x_203_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_newNode_207_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_array_set(v_entries_205_, v_j_185_, v___x_210_);
lean_dec(v_j_185_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_211_);
v___x_213_ = v___x_199_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_val_216_; lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_newNode_207_);
lean_del_object(v___x_203_);
v_val_216_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v___x_208_);
v_fst_217_ = lean_ctor_get(v_val_216_, 0);
v_snd_218_ = lean_ctor_get(v_val_216_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_val_216_);
if (v_isSharedCheck_229_ == 0)
{
v___x_220_ = v_val_216_;
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snd_218_);
lean_inc(v_fst_217_);
lean_dec(v_val_216_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_snd_218_);
v___x_223_ = v_reuseFailAlloc_228_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_array_set(v_entries_205_, v_j_185_, v___x_223_);
lean_dec(v_j_185_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_224_);
v___x_226_ = v___x_199_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_185_);
return v_x_177_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v_vs_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_248_; 
v_ks_233_ = lean_ctor_get(v_x_177_, 0);
v_vs_234_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_248_ == 0)
{
v___x_236_ = v_x_177_;
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_vs_234_);
lean_inc(v_ks_233_);
lean_dec(v_x_177_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_248_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; 
v___x_238_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_ks_233_, v_x_179_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_240_; 
if (v_isShared_237_ == 0)
{
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_ks_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_vs_234_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v_val_242_; lean_object* v_keys_x27_243_; lean_object* v_vals_x27_244_; lean_object* v___x_246_; 
v_val_242_ = lean_ctor_get(v___x_238_, 0);
lean_inc_n(v_val_242_, 2);
lean_dec_ref(v___x_238_);
v_keys_x27_243_ = l_Array_eraseIdx___redArg(v_ks_233_, v_val_242_);
v_vals_x27_244_ = l_Array_eraseIdx___redArg(v_vs_234_, v_val_242_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_vals_x27_244_);
lean_ctor_set(v___x_236_, 0, v_keys_x27_243_);
v___x_246_ = v___x_236_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_keys_x27_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_vals_x27_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
size_t v_x_184__boxed_252_; lean_object* v_res_253_; 
v_x_184__boxed_252_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_253_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_249_, v_x_184__boxed_252_, v_x_251_);
lean_dec(v_x_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint64_t v___y_257_; 
if (lean_obj_tag(v_x_255_) == 0)
{
uint64_t v___x_260_; 
v___x_260_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
v___y_257_ = v___x_260_;
goto v___jp_256_;
}
else
{
uint64_t v_hash_261_; 
v_hash_261_ = lean_ctor_get_uint64(v_x_255_, sizeof(void*)*2);
v___y_257_ = v_hash_261_;
goto v___jp_256_;
}
v___jp_256_:
{
size_t v_h_258_; lean_object* v___x_259_; 
v_h_258_ = lean_uint64_to_usize(v___y_257_);
v___x_259_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_254_, v_h_258_, v_x_255_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_262_, v_x_263_);
lean_dec(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object* v_s_265_, lean_object* v_declName_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_265_, v_declName_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object* v_s_268_, lean_object* v_declName_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Grind_CasesTypes_erase(v_s_268_, v_declName_269_);
lean_dec(v_declName_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object* v_00_u03b2_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object* v_00_u03b2_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(v_00_u03b2_275_, v_x_276_, v_x_277_);
lean_dec(v_x_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object* v_00_u03b2_279_, lean_object* v_x_280_, size_t v_x_281_, lean_object* v_x_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_280_, v_x_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
size_t v_x_349__boxed_288_; lean_object* v_res_289_; 
v_x_349__boxed_288_ = lean_unbox_usize(v_x_286_);
lean_dec(v_x_286_);
v_res_289_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(v_00_u03b2_284_, v_x_285_, v_x_349__boxed_288_, v_x_287_);
lean_dec(v_x_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_290_, lean_object* v_vals_291_, lean_object* v_i_292_, lean_object* v_k_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_keys_290_);
v___x_295_ = lean_nat_dec_lt(v_i_292_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec(v_i_292_);
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v_k_x27_297_; uint8_t v___x_298_; 
v_k_x27_297_ = lean_array_fget_borrowed(v_keys_290_, v_i_292_);
v___x_298_ = lean_name_eq(v_k_293_, v_k_x27_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_i_292_, v___x_299_);
lean_dec(v_i_292_);
v_i_292_ = v___x_300_;
goto _start;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_array_fget_borrowed(v_vals_291_, v_i_292_);
lean_dec(v_i_292_);
lean_inc(v___x_302_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_304_, lean_object* v_vals_305_, lean_object* v_i_306_, lean_object* v_k_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_304_, v_vals_305_, v_i_306_, v_k_307_);
lean_dec(v_k_307_);
lean_dec_ref(v_vals_305_);
lean_dec_ref(v_keys_304_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_309_, size_t v_x_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v_es_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_333_; 
v_es_312_ = lean_ctor_get(v_x_309_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_333_ == 0)
{
v___x_314_ = v_x_309_;
v_isShared_315_ = v_isSharedCheck_333_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_es_312_);
lean_dec(v_x_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_333_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v_j_320_; lean_object* v___x_321_; 
v___x_316_ = lean_box(2);
v___x_317_ = ((size_t)5ULL);
v___x_318_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
v___x_319_ = lean_usize_land(v_x_310_, v___x_318_);
v_j_320_ = lean_usize_to_nat(v___x_319_);
v___x_321_ = lean_array_get(v___x_316_, v_es_312_, v_j_320_);
lean_dec(v_j_320_);
lean_dec_ref(v_es_312_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_object* v_key_322_; lean_object* v_val_323_; uint8_t v___x_324_; 
v_key_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_key_322_);
v_val_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_val_323_);
lean_dec_ref(v___x_321_);
v___x_324_ = lean_name_eq(v_x_311_, v_key_322_);
lean_dec(v_key_322_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_val_323_);
lean_del_object(v___x_314_);
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v___x_327_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v_val_323_);
v___x_327_ = v___x_314_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_val_323_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
case 1:
{
lean_object* v_node_329_; size_t v___x_330_; 
lean_del_object(v___x_314_);
v_node_329_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_node_329_);
lean_dec_ref(v___x_321_);
v___x_330_ = lean_usize_shift_right(v_x_310_, v___x_317_);
v_x_309_ = v_node_329_;
v_x_310_ = v___x_330_;
goto _start;
}
default: 
{
lean_object* v___x_332_; 
lean_del_object(v___x_314_);
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
}
}
else
{
lean_object* v_ks_334_; lean_object* v_vs_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_ks_334_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_ks_334_);
v_vs_335_ = lean_ctor_get(v_x_309_, 1);
lean_inc_ref(v_vs_335_);
lean_dec_ref(v_x_309_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_334_, v_vs_335_, v___x_336_, v_x_311_);
lean_dec_ref(v_vs_335_);
lean_dec_ref(v_ks_334_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
size_t v_x_147__boxed_341_; lean_object* v_res_342_; 
v_x_147__boxed_341_ = lean_unbox_usize(v_x_339_);
lean_dec(v_x_339_);
v_res_342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_338_, v_x_147__boxed_341_, v_x_340_);
lean_dec(v_x_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
uint64_t v___y_346_; 
if (lean_obj_tag(v_x_344_) == 0)
{
uint64_t v___x_349_; 
v___x_349_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
v___y_346_ = v___x_349_;
goto v___jp_345_;
}
else
{
uint64_t v_hash_350_; 
v_hash_350_ = lean_ctor_get_uint64(v_x_344_, sizeof(void*)*2);
v___y_346_ = v_hash_350_;
goto v___jp_345_;
}
v___jp_345_:
{
size_t v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_uint64_to_usize(v___y_346_);
v___x_348_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_343_, v___x_347_, v_x_344_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_351_, v_x_352_);
lean_dec(v_x_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object* v_s_354_, lean_object* v_declName_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_354_, v_declName_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object* v_s_357_, lean_object* v_declName_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Grind_CasesTypes_find_x3f(v_s_357_, v_declName_358_);
lean_dec(v_declName_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object* v_00_u03b2_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(v_00_u03b2_364_, v_x_365_, v_x_366_);
lean_dec(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_368_, lean_object* v_x_369_, size_t v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_369_, v_x_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
size_t v_x_237__boxed_377_; lean_object* v_res_378_; 
v_x_237__boxed_377_ = lean_unbox_usize(v_x_375_);
lean_dec(v_x_375_);
v_res_378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(v_00_u03b2_373_, v_x_374_, v_x_237__boxed_377_, v_x_376_);
lean_dec(v_x_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_379_, lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_heq_382_, lean_object* v_i_383_, lean_object* v_k_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_380_, v_vals_381_, v_i_383_, v_k_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_386_, lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_heq_389_, lean_object* v_i_390_, lean_object* v_k_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_386_, v_keys_387_, v_vals_388_, v_heq_389_, v_i_390_, v_k_391_);
lean_dec(v_k_391_);
lean_dec_ref(v_vals_388_);
lean_dec_ref(v_keys_387_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object* v_s_393_, lean_object* v_declName_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_393_, v_declName_394_);
if (lean_obj_tag(v___x_395_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_394_);
return v___x_396_;
}
else
{
lean_object* v_val_397_; uint8_t v___x_398_; 
v_val_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v___x_395_);
v___x_398_ = lean_unbox(v_val_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
lean_dec(v_val_397_);
v___x_399_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_394_);
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_unbox(v_val_397_);
lean_dec(v_val_397_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object* v_s_401_, lean_object* v_declName_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_401_, v_declName_402_);
lean_dec(v_declName_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object* v_s_405_, lean_object* v_declName_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_405_, v_declName_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_406_);
return v___x_408_;
}
else
{
uint8_t v___x_409_; 
lean_dec_ref(v___x_407_);
v___x_409_ = 1;
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object* v_s_410_, lean_object* v_declName_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_410_, v_declName_411_);
lean_dec(v_declName_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object* v_declName_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_env_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_env_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_env_418_);
lean_dec(v___x_417_);
v___x_419_ = l_Lean_isInductiveCore_x3f(v_env_418_, v_declName_414_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object* v_declName_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_421_, v___y_422_);
lean_dec(v___y_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object* v_declName_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_425_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object* v_declName_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(v_declName_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object* v_declName_435_, uint8_t v_eager_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_462_; 
lean_inc(v_declName_435_);
v___x_440_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_435_, v_a_438_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_462_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
if (lean_obj_tag(v_a_441_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_459_; 
v_val_450_ = lean_ctor_get(v_a_441_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_459_ == 0)
{
v___x_452_ = v_a_441_;
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v_a_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v_isRec_454_; 
v_isRec_454_ = lean_ctor_get_uint8(v_val_450_, sizeof(void*)*6);
lean_dec(v_val_450_);
if (v_isRec_454_ == 0)
{
lean_del_object(v___x_452_);
goto v___jp_445_;
}
else
{
if (v_eager_436_ == 0)
{
lean_del_object(v___x_452_);
goto v___jp_445_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_del_object(v___x_443_);
lean_dec(v_declName_435_);
v___x_455_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 0);
lean_ctor_set(v___x_452_, 0, v___x_455_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_del_object(v___x_443_);
lean_dec(v_a_441_);
lean_dec(v_declName_435_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_declName_435_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object* v_declName_463_, lean_object* v_eager_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
uint8_t v_eager_boxed_468_; lean_object* v_res_469_; 
v_eager_boxed_468_ = lean_unbox(v_eager_464_);
v_res_469_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_463_, v_eager_boxed_468_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object* v_declName_470_, uint8_t v_eager_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_470_, v_eager_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_490_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_490_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_490_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_490_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
if (lean_obj_tag(v_a_476_) == 0)
{
uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = 0;
v___x_481_ = lean_box(v___x_480_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec_ref(v_a_476_);
v___x_485_ = 1;
v___x_486_ = lean_box(v___x_485_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_486_);
v___x_488_ = v___x_478_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_475_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_475_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object* v_declName_499_, lean_object* v_eager_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
uint8_t v_eager_boxed_504_; lean_object* v_res_505_; 
v_eager_boxed_504_ = lean_unbox(v_eager_500_);
v_res_505_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_499_, v_eager_boxed_504_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object* v_declName_506_, uint8_t v_eager_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_506_, v_eager_507_, v_a_510_, v_a_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_524_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (lean_obj_tag(v_a_514_) == 1)
{
lean_object* v_val_518_; lean_object* v___x_519_; 
lean_del_object(v___x_516_);
v_val_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref(v_a_514_);
v___x_519_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_518_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_a_514_);
v___x_520_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_513_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_513_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object* v_declName_533_, lean_object* v_eager_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
uint8_t v_eager_boxed_540_; lean_object* v_res_541_; 
v_eager_boxed_540_ = lean_unbox(v_eager_534_);
v_res_541_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_533_, v_eager_boxed_540_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_542_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
lean_ctor_set(v___x_547_, 3, v___x_545_);
lean_ctor_set(v___x_547_, 4, v___x_545_);
lean_ctor_set(v___x_547_, 5, v___x_545_);
lean_ctor_set(v___x_547_, 6, v___x_545_);
lean_ctor_set(v___x_547_, 7, v___x_545_);
lean_ctor_set(v___x_547_, 8, v___x_545_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(32u);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = ((size_t)5ULL);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_unsigned_to_nat(32u);
v___x_554_ = lean_mk_empty_array_with_capacity(v___x_553_);
v___x_555_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3);
v___x_556_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_552_);
lean_ctor_set(v___x_556_, 3, v___x_552_);
lean_ctor_set_usize(v___x_556_, 4, v___x_551_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = lean_box(1);
v___x_558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4);
v___x_559_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
lean_ctor_set(v___x_560_, 2, v___x_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_env_566_; lean_object* v_options_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_565_ = lean_st_ref_get(v___y_563_);
v_env_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_env_566_);
lean_dec(v___x_565_);
v_options_567_ = lean_ctor_get(v___y_562_, 2);
v___x_568_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_569_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_567_);
v___x_570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_570_, 0, v_env_566_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_ctor_set(v___x_570_, 3, v_options_567_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_msgData_561_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_ref_582_; lean_object* v___x_583_; lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_ref_582_ = lean_ctor_get(v___y_579_, 5);
v___x_583_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msg_578_, v___y_579_, v___y_580_);
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_inc(v_ref_582_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_ref_582_);
lean_ctor_set(v___x_588_, 1, v_a_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_597_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__0));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__2));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__4));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__6));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object* v_declName_610_, uint8_t v_eager_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; 
lean_inc(v_declName_610_);
v___x_615_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_610_, v_eager_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_638_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_638_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_638_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_638_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_unbox(v_a_616_);
if (v___x_620_ == 0)
{
lean_del_object(v___x_618_);
if (v_eager_611_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_a_616_);
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__1, &l_Lean_Meta_Grind_validateCasesAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1);
v___x_622_ = l_Lean_MessageData_ofConstName(v_declName_610_, v_eager_611_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__3, &l_Lean_Meta_Grind_validateCasesAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_625_, v_a_612_, v_a_613_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__5, &l_Lean_Meta_Grind_validateCasesAttr___closed__5_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5);
v___x_628_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
v___x_629_ = l_Lean_MessageData_ofConstName(v_declName_610_, v___x_628_);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_627_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__7, &l_Lean_Meta_Grind_validateCasesAttr___closed__7_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_632_, v_a_612_, v_a_613_);
return v___x_633_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_a_616_);
lean_dec(v_declName_610_);
v___x_634_ = lean_box(0);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_634_);
v___x_636_ = v___x_618_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_declName_610_);
v_a_639_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_615_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_615_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object* v_declName_647_, lean_object* v_eager_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
uint8_t v_eager_boxed_652_; lean_object* v_res_653_; 
v_eager_boxed_652_ = lean_unbox(v_eager_648_);
v_res_653_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_647_, v_eager_boxed_652_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_655_, v___y_656_, v___y_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(v_00_u03b1_660_, v_msg_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object* v_s_666_, lean_object* v_declName_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_666_, v_declName_667_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_dec_ref(v_s_666_);
v___x_672_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_667_, v_a_668_, v_a_669_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_666_, v_declName_667_);
lean_dec(v_declName_667_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object* v_s_675_, lean_object* v_declName_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_675_, v_declName_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object* v_declName_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_687_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_declName_687_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_694_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_695_ = 0;
v___x_696_ = l_Lean_MessageData_ofConstName(v_declName_687_, v___x_695_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_699_, v_a_688_, v_a_689_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object* v_declName_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object* v_e_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
if (lean_obj_tag(v_e_706_) == 1)
{
lean_object* v_fvarId_712_; lean_object* v___x_713_; 
v_fvarId_712_ = lean_ctor_get(v_e_706_, 0);
lean_inc(v_fvarId_712_);
lean_dec_ref(v_e_706_);
v___x_713_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_712_, v_a_707_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_730_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_730_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_730_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_730_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_lctx_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_lctx_718_ = lean_ctor_get(v_a_707_, 2);
v___x_719_ = l_Lean_LocalDecl_index(v_a_714_);
lean_inc_ref(v_lctx_718_);
v___x_720_ = lean_local_ctx_num_indices(v_lctx_718_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_sub(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_nat_dec_eq(v___x_719_, v___x_722_);
lean_dec(v___x_722_);
lean_dec(v___x_719_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_del_object(v___x_716_);
v___x_724_ = l_Lean_LocalDecl_type(v_a_714_);
lean_dec(v_a_714_);
v___x_725_ = l_Lean_Meta_isProp(v___x_724_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec(v_a_714_);
v___x_726_ = lean_box(v___x_723_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_726_);
v___x_728_ = v___x_716_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_713_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_713_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref(v_e_706_);
v___x_739_ = 0;
v___x_740_ = lean_box(v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_748_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object* v_mvarId_757_, lean_object* v_e_758_, lean_object* v_type_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4);
v___x_767_ = l_Lean_MessageData_ofExpr(v_e_758_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_indentExpr(v_type_759_);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = l_Lean_Meta_throwTacticEx___redArg(v___x_765_, v_mvarId_757_, v___x_771_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object* v_mvarId_773_, lean_object* v_e_774_, lean_object* v_type_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_773_, v_e_774_, v_type_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object* v_mvarId_782_, lean_object* v_e_783_, lean_object* v_00_u03b1_784_, lean_object* v_type_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_782_, v_e_783_, v_type_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object* v_mvarId_792_, lean_object* v_e_793_, lean_object* v_00_u03b1_794_, lean_object* v_type_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(v_mvarId_792_, v_e_793_, v_00_u03b1_794_, v_type_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object* v_mvarId_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_809_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_809_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_826_, v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object* v_00_u03b1_834_, lean_object* v_mvarId_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_835_, v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object* v_00_u03b1_843_, lean_object* v_mvarId_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(v_00_u03b1_843_, v_mvarId_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object* v_as_852_, size_t v_i_853_, size_t v_stop_854_, lean_object* v_b_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_eq(v_i_853_, v_stop_854_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; size_t v___x_860_; size_t v___x_861_; 
v___x_857_ = 1;
v___x_858_ = lean_array_uget_borrowed(v_as_852_, v_i_853_);
lean_inc(v___x_858_);
v___x_859_ = l_Lean_LocalContext_setKind(v_b_855_, v___x_858_, v___x_857_);
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_853_, v___x_860_);
v_i_853_ = v___x_861_;
v_b_855_ = v___x_859_;
goto _start;
}
else
{
return v_b_855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object* v_as_863_, lean_object* v_i_864_, lean_object* v_stop_865_, lean_object* v_b_866_){
_start:
{
size_t v_i_boxed_867_; size_t v_stop_boxed_868_; lean_object* v_res_869_; 
v_i_boxed_867_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_stop_boxed_868_ = lean_unbox_usize(v_stop_865_);
lean_dec(v_stop_865_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_863_, v_i_boxed_867_, v_stop_boxed_868_, v_b_866_);
lean_dec_ref(v_as_863_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_ks_874_; lean_object* v_vs_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_899_; 
v_ks_874_ = lean_ctor_get(v_x_870_, 0);
v_vs_875_ = lean_ctor_get(v_x_870_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_870_);
if (v_isSharedCheck_899_ == 0)
{
v___x_877_ = v_x_870_;
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_vs_875_);
lean_inc(v_ks_874_);
lean_dec(v_x_870_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_ks_874_);
v___x_880_ = lean_nat_dec_lt(v_x_871_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_x_871_);
v___x_881_ = lean_array_push(v_ks_874_, v_x_872_);
v___x_882_ = lean_array_push(v_vs_875_, v_x_873_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_882_);
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v_k_x27_886_; uint8_t v___x_887_; 
v_k_x27_886_ = lean_array_fget_borrowed(v_ks_874_, v_x_871_);
v___x_887_ = l_Lean_instBEqMVarId_beq(v_x_872_, v_k_x27_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_889_; 
if (v_isShared_878_ == 0)
{
v___x_889_ = v___x_877_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_ks_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_vs_875_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_add(v_x_871_, v___x_890_);
lean_dec(v_x_871_);
v_x_870_ = v___x_889_;
v_x_871_ = v___x_891_;
goto _start;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_894_ = lean_array_fset(v_ks_874_, v_x_871_, v_x_872_);
v___x_895_ = lean_array_fset(v_vs_875_, v_x_871_, v_x_873_);
lean_dec(v_x_871_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_895_);
lean_ctor_set(v___x_877_, 0, v___x_894_);
v___x_897_ = v___x_877_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object* v_n_900_, lean_object* v_k_901_, lean_object* v_v_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_n_900_, v___x_903_, v_k_901_, v_v_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object* v_x_906_, size_t v_x_907_, size_t v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v_es_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v_j_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_es_911_ = lean_ctor_get(v_x_906_, 0);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
v___x_915_ = lean_usize_land(v_x_907_, v___x_914_);
v_j_916_ = lean_usize_to_nat(v___x_915_);
v___x_917_ = lean_array_get_size(v_es_911_);
v___x_918_ = lean_nat_dec_lt(v_j_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec(v_j_916_);
lean_dec(v_x_910_);
lean_dec(v_x_909_);
return v_x_906_;
}
else
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_955_; 
lean_inc_ref(v_es_911_);
v_isSharedCheck_955_ = !lean_is_exclusive(v_x_906_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_x_906_, 0);
lean_dec(v_unused_956_);
v___x_920_ = v_x_906_;
v_isShared_921_ = v_isSharedCheck_955_;
goto v_resetjp_919_;
}
else
{
lean_dec(v_x_906_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_955_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_v_922_; lean_object* v___x_923_; lean_object* v_xs_x27_924_; lean_object* v___y_926_; 
v_v_922_ = lean_array_fget(v_es_911_, v_j_916_);
v___x_923_ = lean_box(0);
v_xs_x27_924_ = lean_array_fset(v_es_911_, v_j_916_, v___x_923_);
switch(lean_obj_tag(v_v_922_))
{
case 0:
{
lean_object* v_key_931_; lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_942_; 
v_key_931_ = lean_ctor_get(v_v_922_, 0);
v_val_932_ = lean_ctor_get(v_v_922_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_v_922_);
if (v_isSharedCheck_942_ == 0)
{
v___x_934_ = v_v_922_;
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_inc(v_key_931_);
lean_dec(v_v_922_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v___x_936_; 
v___x_936_ = l_Lean_instBEqMVarId_beq(v_x_909_, v_key_931_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_del_object(v___x_934_);
v___x_937_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_931_, v_val_932_, v_x_909_, v_x_910_);
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
v___y_926_ = v___x_938_;
goto v___jp_925_;
}
else
{
lean_object* v___x_940_; 
lean_dec(v_val_932_);
lean_dec(v_key_931_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_x_910_);
lean_ctor_set(v___x_934_, 0, v_x_909_);
v___x_940_ = v___x_934_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_x_909_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_x_910_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v___y_926_ = v___x_940_;
goto v___jp_925_;
}
}
}
}
case 1:
{
lean_object* v_node_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_node_943_ = lean_ctor_get(v_v_922_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_v_922_);
if (v_isSharedCheck_953_ == 0)
{
v___x_945_ = v_v_922_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_node_943_);
lean_dec(v_v_922_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_947_ = lean_usize_shift_right(v_x_907_, v___x_912_);
v___x_948_ = lean_usize_add(v_x_908_, v___x_913_);
v___x_949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_node_943_, v___x_947_, v___x_948_, v_x_909_, v_x_910_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
v___y_926_ = v___x_951_;
goto v___jp_925_;
}
}
}
default: 
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_x_909_);
lean_ctor_set(v___x_954_, 1, v_x_910_);
v___y_926_ = v___x_954_;
goto v___jp_925_;
}
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_array_fset(v_xs_x27_924_, v_j_916_, v___y_926_);
lean_dec(v_j_916_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_927_);
v___x_929_ = v___x_920_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v_ks_957_; lean_object* v_vs_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_978_; 
v_ks_957_ = lean_ctor_get(v_x_906_, 0);
v_vs_958_ = lean_ctor_get(v_x_906_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_906_);
if (v_isSharedCheck_978_ == 0)
{
v___x_960_ = v_x_906_;
v_isShared_961_ = v_isSharedCheck_978_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_vs_958_);
lean_inc(v_ks_957_);
lean_dec(v_x_906_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_978_;
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
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_ks_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_vs_958_);
v___x_963_ = v_reuseFailAlloc_977_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v_newNode_964_; uint8_t v___y_966_; size_t v___x_972_; uint8_t v___x_973_; 
v_newNode_964_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v___x_963_, v_x_909_, v_x_910_);
v___x_972_ = ((size_t)7ULL);
v___x_973_ = lean_usize_dec_le(v___x_972_, v_x_908_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_964_);
v___x_975_ = lean_unsigned_to_nat(4u);
v___x_976_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
lean_dec(v___x_974_);
v___y_966_ = v___x_976_;
goto v___jp_965_;
}
else
{
v___y_966_ = v___x_973_;
goto v___jp_965_;
}
v___jp_965_:
{
if (v___y_966_ == 0)
{
lean_object* v_ks_967_; lean_object* v_vs_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_ks_967_ = lean_ctor_get(v_newNode_964_, 0);
lean_inc_ref(v_ks_967_);
v_vs_968_ = lean_ctor_get(v_newNode_964_, 1);
lean_inc_ref(v_vs_968_);
lean_dec_ref(v_newNode_964_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_x_908_, v_ks_967_, v_vs_968_, v___x_969_, v___x_970_);
lean_dec_ref(v_vs_968_);
lean_dec_ref(v_ks_967_);
return v___x_971_;
}
else
{
return v_newNode_964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t v_depth_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_i_982_, lean_object* v_entries_983_){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_array_get_size(v_keys_980_);
v___x_985_ = lean_nat_dec_lt(v_i_982_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec(v_i_982_);
return v_entries_983_;
}
else
{
lean_object* v_k_986_; lean_object* v_v_987_; uint64_t v___x_988_; size_t v_h_989_; size_t v___x_990_; lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v_h_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_k_986_ = lean_array_fget_borrowed(v_keys_980_, v_i_982_);
v_v_987_ = lean_array_fget_borrowed(v_vals_981_, v_i_982_);
v___x_988_ = l_Lean_instHashableMVarId_hash(v_k_986_);
v_h_989_ = lean_uint64_to_usize(v___x_988_);
v___x_990_ = ((size_t)5ULL);
v___x_991_ = lean_unsigned_to_nat(1u);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_sub(v_depth_979_, v___x_992_);
v___x_994_ = lean_usize_mul(v___x_990_, v___x_993_);
v_h_995_ = lean_usize_shift_right(v_h_989_, v___x_994_);
v___x_996_ = lean_nat_add(v_i_982_, v___x_991_);
lean_dec(v_i_982_);
lean_inc(v_v_987_);
lean_inc(v_k_986_);
v___x_997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_entries_983_, v_h_995_, v_depth_979_, v_k_986_, v_v_987_);
v_i_982_ = v___x_996_;
v_entries_983_ = v___x_997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object* v_depth_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_i_1002_, lean_object* v_entries_1003_){
_start:
{
size_t v_depth_boxed_1004_; lean_object* v_res_1005_; 
v_depth_boxed_1004_ = lean_unbox_usize(v_depth_999_);
lean_dec(v_depth_999_);
v_res_1005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_boxed_1004_, v_keys_1000_, v_vals_1001_, v_i_1002_, v_entries_1003_);
lean_dec_ref(v_vals_1001_);
lean_dec_ref(v_keys_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
size_t v_x_12383__boxed_1011_; size_t v_x_12384__boxed_1012_; lean_object* v_res_1013_; 
v_x_12383__boxed_1011_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_x_12384__boxed_1012_ = lean_unbox_usize(v_x_1008_);
lean_dec(v_x_1008_);
v_res_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1006_, v_x_12383__boxed_1011_, v_x_12384__boxed_1012_, v_x_1009_, v_x_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
uint64_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = l_Lean_instHashableMVarId_hash(v_x_1015_);
v___x_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1014_, v___x_1018_, v___x_1019_, v_x_1015_, v_x_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object* v_mvarId_1021_, lean_object* v_val_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_mctx_1026_; lean_object* v_cache_1027_; lean_object* v_zetaDeltaFVarIds_1028_; lean_object* v_postponed_1029_; lean_object* v_diag_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1057_; 
v___x_1025_ = lean_st_ref_take(v___y_1023_);
v_mctx_1026_ = lean_ctor_get(v___x_1025_, 0);
v_cache_1027_ = lean_ctor_get(v___x_1025_, 1);
v_zetaDeltaFVarIds_1028_ = lean_ctor_get(v___x_1025_, 2);
v_postponed_1029_ = lean_ctor_get(v___x_1025_, 3);
v_diag_1030_ = lean_ctor_get(v___x_1025_, 4);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1032_ = v___x_1025_;
v_isShared_1033_ = v_isSharedCheck_1057_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_diag_1030_);
lean_inc(v_postponed_1029_);
lean_inc(v_zetaDeltaFVarIds_1028_);
lean_inc(v_cache_1027_);
lean_inc(v_mctx_1026_);
lean_dec(v___x_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1057_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_depth_1034_; lean_object* v_levelAssignDepth_1035_; lean_object* v_mvarCounter_1036_; lean_object* v_lDepth_1037_; lean_object* v_decls_1038_; lean_object* v_userNames_1039_; lean_object* v_lAssignment_1040_; lean_object* v_eAssignment_1041_; lean_object* v_dAssignment_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1056_; 
v_depth_1034_ = lean_ctor_get(v_mctx_1026_, 0);
v_levelAssignDepth_1035_ = lean_ctor_get(v_mctx_1026_, 1);
v_mvarCounter_1036_ = lean_ctor_get(v_mctx_1026_, 2);
v_lDepth_1037_ = lean_ctor_get(v_mctx_1026_, 3);
v_decls_1038_ = lean_ctor_get(v_mctx_1026_, 4);
v_userNames_1039_ = lean_ctor_get(v_mctx_1026_, 5);
v_lAssignment_1040_ = lean_ctor_get(v_mctx_1026_, 6);
v_eAssignment_1041_ = lean_ctor_get(v_mctx_1026_, 7);
v_dAssignment_1042_ = lean_ctor_get(v_mctx_1026_, 8);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_mctx_1026_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1044_ = v_mctx_1026_;
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_dAssignment_1042_);
lean_inc(v_eAssignment_1041_);
lean_inc(v_lAssignment_1040_);
lean_inc(v_userNames_1039_);
lean_inc(v_decls_1038_);
lean_inc(v_lDepth_1037_);
lean_inc(v_mvarCounter_1036_);
lean_inc(v_levelAssignDepth_1035_);
lean_inc(v_depth_1034_);
lean_dec(v_mctx_1026_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_eAssignment_1041_, v_mvarId_1021_, v_val_1022_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 7, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_depth_1034_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_levelAssignDepth_1035_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_mvarCounter_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v_lDepth_1037_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_decls_1038_);
lean_ctor_set(v_reuseFailAlloc_1055_, 5, v_userNames_1039_);
lean_ctor_set(v_reuseFailAlloc_1055_, 6, v_lAssignment_1040_);
lean_ctor_set(v_reuseFailAlloc_1055_, 7, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1055_, 8, v_dAssignment_1042_);
v___x_1048_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1048_);
v___x_1050_ = v___x_1032_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_cache_1027_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_zetaDeltaFVarIds_1028_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_postponed_1029_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_diag_1030_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_st_ref_set(v___y_1023_, v___x_1050_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object* v_mvarId_1058_, lean_object* v_val_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1058_, v_val_1059_, v___y_1060_);
lean_dec(v___y_1060_);
return v_res_1062_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1));
v___x_1067_ = l_Lean_MessageData_ofFormat(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object* v_upperBound_1070_, lean_object* v___y_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_a_1074_, lean_object* v_mvarId_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_lt(v_a_1076_, v_upperBound_1070_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_a_1076_);
lean_dec(v_mvarId_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___y_1071_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_b_1077_);
return v___x_1084_;
}
else
{
lean_object* v_snd_1085_; lean_object* v_fst_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1168_; 
v_snd_1085_ = lean_ctor_get(v_b_1077_, 1);
v_fst_1086_ = lean_ctor_get(v_b_1077_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_b_1077_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1088_ = v_b_1077_;
v_isShared_1089_ = v_isSharedCheck_1168_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1086_);
lean_dec(v_b_1077_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1168_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1167_; 
v_fst_1090_ = lean_ctor_get(v_snd_1085_, 0);
v_snd_1091_ = lean_ctor_get(v_snd_1085_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_snd_1085_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1093_ = v_snd_1085_;
v_isShared_1094_ = v_isSharedCheck_1167_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_inc(v_fst_1090_);
lean_dec(v_snd_1085_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1167_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; 
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v_fst_1090_);
v___x_1095_ = lean_whnf(v_fst_1090_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1158_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v_fst_1097_ = lean_ctor_get(v_snd_1091_, 0);
v_snd_1098_ = lean_ctor_get(v_snd_1091_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_snd_1091_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1100_ = v_snd_1091_;
v_isShared_1101_ = v_isSharedCheck_1158_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_snd_1098_);
lean_inc(v_fst_1097_);
lean_dec(v_snd_1091_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1158_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v_a_1104_; 
v___x_1102_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_a_1096_) == 7)
{
lean_object* v_binderType_1107_; lean_object* v_body_1108_; lean_object* v___x_1109_; lean_object* v___y_1111_; uint8_t v___x_1136_; 
lean_dec(v_fst_1090_);
v_binderType_1107_ = lean_ctor_get(v_a_1096_, 1);
lean_inc_ref(v_binderType_1107_);
v_body_1108_ = lean_ctor_get(v_a_1096_, 2);
lean_inc_ref(v_body_1108_);
lean_dec_ref(v_a_1096_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_lt(v___x_1102_, v___x_1073_);
if (v___x_1136_ == 0)
{
lean_inc(v_a_1074_);
v___y_1111_ = v_a_1074_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1137_; 
lean_inc(v_snd_1098_);
lean_inc(v_a_1074_);
v___x_1137_ = l_Lean_Name_num___override(v_a_1074_, v_snd_1098_);
v___y_1111_ = v___x_1137_;
goto v___jp_1110_;
}
v___jp_1110_:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = 2;
lean_inc_ref(v___x_1072_);
lean_inc_ref(v___y_1071_);
v___x_1113_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_1071_, v___x_1072_, v_binderType_1107_, v___x_1112_, v___y_1111_, v___x_1109_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_n(v_a_1114_, 2);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_Lean_Expr_app___override(v_fst_1086_, v_a_1114_);
v___x_1116_ = l_Lean_Expr_mvarId_x21(v_a_1114_);
lean_dec(v_a_1114_);
v___x_1117_ = lean_array_push(v_fst_1097_, v___x_1116_);
v___x_1118_ = lean_nat_add(v_snd_1098_, v___x_1102_);
lean_dec(v_snd_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1118_);
lean_ctor_set(v___x_1100_, 0, v___x_1117_);
v___x_1120_ = v___x_1100_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1120_);
lean_ctor_set(v___x_1093_, 0, v_body_1108_);
v___x_1122_ = v___x_1093_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_body_1108_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1122_);
lean_ctor_set(v___x_1088_, 0, v___x_1115_);
v___x_1124_ = v___x_1088_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_a_1104_ = v___x_1124_;
goto v___jp_1103_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_body_1108_);
lean_del_object(v___x_1100_);
lean_dec(v_snd_1098_);
lean_dec(v_fst_1097_);
lean_del_object(v___x_1093_);
lean_del_object(v___x_1088_);
lean_dec(v_fst_1086_);
lean_dec(v_a_1076_);
lean_dec(v_mvarId_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___y_1071_);
v_a_1128_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1113_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1113_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_a_1096_);
v___x_1138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_1139_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3);
lean_inc(v_mvarId_1075_);
v___x_1140_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1138_, v_mvarId_1075_, v___x_1139_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref(v___x_1140_);
if (v_isShared_1101_ == 0)
{
v___x_1142_ = v___x_1100_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fst_1097_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1098_);
v___x_1142_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1142_);
v___x_1144_ = v___x_1093_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1090_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1144_);
v___x_1146_ = v___x_1088_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_fst_1086_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v_a_1104_ = v___x_1146_;
goto v___jp_1103_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_del_object(v___x_1100_);
lean_dec(v_snd_1098_);
lean_dec(v_fst_1097_);
lean_del_object(v___x_1093_);
lean_dec(v_fst_1090_);
lean_del_object(v___x_1088_);
lean_dec(v_fst_1086_);
lean_dec(v_a_1076_);
lean_dec(v_mvarId_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___y_1071_);
v_a_1150_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1140_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1140_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_nat_add(v_a_1076_, v___x_1102_);
lean_dec(v_a_1076_);
v_a_1076_ = v___x_1105_;
v_b_1077_ = v_a_1104_;
goto _start;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_del_object(v___x_1093_);
lean_dec(v_snd_1091_);
lean_dec(v_fst_1090_);
lean_del_object(v___x_1088_);
lean_dec(v_fst_1086_);
lean_dec(v_a_1076_);
lean_dec(v_mvarId_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___y_1071_);
v_a_1159_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1095_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1095_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object* v_upperBound_1169_, lean_object* v___y_1170_, lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v_a_1173_, lean_object* v_mvarId_1174_, lean_object* v_a_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1169_, v___y_1170_, v___x_1171_, v___x_1172_, v_a_1173_, v_mvarId_1174_, v_a_1175_, v_b_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___x_1172_);
lean_dec(v_upperBound_1169_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t v_sz_1183_, size_t v_i_1184_, lean_object* v_bs_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_lt(v_i_1184_, v_sz_1183_);
if (v___x_1186_ == 0)
{
return v_bs_1185_;
}
else
{
lean_object* v_v_1187_; lean_object* v___x_1188_; lean_object* v_bs_x27_1189_; lean_object* v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v_v_1187_ = lean_array_uget(v_bs_1185_, v_i_1184_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v_bs_x27_1189_ = lean_array_uset(v_bs_1185_, v_i_1184_, v___x_1188_);
v___x_1190_ = l_Lean_mkFVar(v_v_1187_);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_add(v_i_1184_, v___x_1191_);
v___x_1193_ = lean_array_uset(v_bs_x27_1189_, v_i_1184_, v___x_1190_);
v_i_1184_ = v___x_1192_;
v_bs_1185_ = v___x_1193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object* v_sz_1195_, lean_object* v_i_1196_, lean_object* v_bs_1197_){
_start:
{
size_t v_sz_boxed_1198_; size_t v_i_boxed_1199_; lean_object* v_res_1200_; 
v_sz_boxed_1198_ = lean_unbox_usize(v_sz_1195_);
lean_dec(v_sz_1195_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_boxed_1198_, v_i_boxed_1199_, v_bs_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_mvarId_1208_, lean_object* v_fvarId_1209_, lean_object* v_indices_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_sz_1216_ = lean_array_size(v_indices_1210_);
v___x_1217_ = ((size_t)0ULL);
lean_inc_ref(v_indices_1210_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_1216_, v___x_1217_, v_indices_1210_);
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc_ref(v_a_1206_);
lean_inc(v_fvarId_1209_);
lean_inc(v_mvarId_1208_);
v___x_1220_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_1208_, v___x_1219_, v_fvarId_1209_, v_a_1206_, v___x_1218_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_lctx_1222_; lean_object* v_localInstances_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___y_1228_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v_lctx_1222_ = lean_ctor_get(v___y_1211_, 2);
v_localInstances_1223_ = lean_ctor_get(v___y_1211_, 3);
v___x_1224_ = 1;
lean_inc(v_fvarId_1209_);
lean_inc_ref(v_lctx_1222_);
v___x_1225_ = l_Lean_LocalContext_setKind(v_lctx_1222_, v_fvarId_1209_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_array_get_size(v_indices_1210_);
v___x_1271_ = lean_nat_dec_lt(v___x_1226_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v_indices_1210_);
v___y_1228_ = v___x_1225_;
goto v___jp_1227_;
}
else
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_nat_dec_le(v___x_1270_, v___x_1270_);
if (v___x_1272_ == 0)
{
if (v___x_1271_ == 0)
{
lean_dec_ref(v_indices_1210_);
v___y_1228_ = v___x_1225_;
goto v___jp_1227_;
}
else
{
size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_usize_of_nat(v___x_1270_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1210_, v___x_1217_, v___x_1273_, v___x_1225_);
lean_dec_ref(v_indices_1210_);
v___y_1228_ = v___x_1274_;
goto v___jp_1227_;
}
}
else
{
size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_usize_of_nat(v___x_1270_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1210_, v___x_1217_, v___x_1275_, v___x_1225_);
lean_dec_ref(v_indices_1210_);
v___y_1228_ = v___x_1276_;
goto v___jp_1227_;
}
}
v___jp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = l_Lean_mkAppN(v_a_1221_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1230_ = l_Lean_mkFVar(v_fvarId_1209_);
v___x_1231_ = l_Lean_Expr_app___override(v___x_1229_, v___x_1230_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc_ref(v___x_1231_);
v___x_1232_ = lean_infer_type(v___x_1231_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_Meta_RecursorInfo_numMinors(v_a_1206_);
lean_dec_ref(v_a_1206_);
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__1));
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_a_1233_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
lean_inc(v_mvarId_1208_);
lean_inc_ref(v_localInstances_1223_);
v___x_1238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v___x_1234_, v___y_1228_, v_localInstances_1223_, v___x_1234_, v_a_1207_, v_mvarId_1208_, v___x_1226_, v___x_1237_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___x_1234_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v_fst_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_fst_1240_);
v_snd_1241_ = lean_ctor_get(v_a_1239_, 1);
lean_inc(v_snd_1241_);
lean_dec(v_a_1239_);
v___x_1242_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1208_, v_fst_1240_, v___y_1212_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1253_);
v___x_1244_ = v___x_1242_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v___x_1242_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_snd_1246_; lean_object* v_fst_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_snd_1246_ = lean_ctor_get(v_snd_1241_, 1);
lean_inc(v_snd_1246_);
lean_dec(v_snd_1241_);
v_fst_1247_ = lean_ctor_get(v_snd_1246_, 0);
lean_inc(v_fst_1247_);
lean_dec(v_snd_1246_);
v___x_1248_ = lean_array_to_list(v_fst_1247_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1248_);
v___x_1250_ = v___x_1244_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_mvarId_1208_);
v_a_1254_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1238_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1238_);
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
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___x_1231_);
lean_dec_ref(v___y_1228_);
lean_dec(v_mvarId_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
v_a_1262_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1232_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1232_);
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
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v___x_1218_);
lean_dec_ref(v_indices_1210_);
lean_dec(v_fvarId_1209_);
lean_dec(v_mvarId_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
v_a_1277_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1220_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1220_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_mvarId_1287_, lean_object* v_fvarId_1288_, lean_object* v_indices_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1285_, v_a_1286_, v_mvarId_1287_, v_fvarId_1288_, v_indices_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8));
v___x_1310_ = l_Lean_stringToMessageData(v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1317_, lean_object* v_declHint_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v_env_1322_; uint8_t v___x_1323_; 
v___x_1321_ = lean_st_ref_get(v___y_1319_);
v_env_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_env_1322_);
lean_dec(v___x_1321_);
v___x_1323_ = l_Lean_Name_isAnonymous(v_declHint_1318_);
if (v___x_1323_ == 0)
{
uint8_t v_isExporting_1324_; 
v_isExporting_1324_ = lean_ctor_get_uint8(v_env_1322_, sizeof(void*)*8);
if (v_isExporting_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref(v_env_1322_);
lean_dec(v_declHint_1318_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_msg_1317_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_inc_ref(v_env_1322_);
v___x_1326_ = l_Lean_Environment_setExporting(v_env_1322_, v___x_1323_);
lean_inc(v_declHint_1318_);
lean_inc_ref(v___x_1326_);
v___x_1327_ = l_Lean_Environment_contains(v___x_1326_, v_declHint_1318_, v_isExporting_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref(v___x_1326_);
lean_dec_ref(v_env_1322_);
lean_dec(v_declHint_1318_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_msg_1317_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_c_1334_; lean_object* v___x_1335_; 
v___x_1329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_1330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
v___x_1331_ = l_Lean_Options_empty;
v___x_1332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1326_);
lean_ctor_set(v___x_1332_, 1, v___x_1329_);
lean_ctor_set(v___x_1332_, 2, v___x_1330_);
lean_ctor_set(v___x_1332_, 3, v___x_1331_);
lean_inc(v_declHint_1318_);
v___x_1333_ = l_Lean_MessageData_ofConstName(v_declHint_1318_, v___x_1323_);
v_c_1334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1334_, 0, v___x_1332_);
lean_ctor_set(v_c_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1322_, v_declHint_1318_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_env_1322_);
lean_dec(v_declHint_1318_);
v___x_1336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v_c_1334_);
v___x_1338_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_MessageData_note(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_msg_1317_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
else
{
lean_object* v_val_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1378_; 
v_val_1343_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1345_ = v___x_1335_;
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_val_1343_);
lean_dec(v___x_1335_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1378_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_mod_1350_; uint8_t v___x_1351_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = l_Lean_Environment_header(v_env_1322_);
lean_dec_ref(v_env_1322_);
v___x_1349_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1348_);
v_mod_1350_ = lean_array_get(v___x_1347_, v___x_1349_, v_val_1343_);
lean_dec(v_val_1343_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = l_Lean_isPrivateName(v_declHint_1318_);
lean_dec(v_declHint_1318_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_c_1334_);
v___x_1354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_MessageData_ofName(v_mod_1350_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_MessageData_note(v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_msg_1317_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1361_);
v___x_1363_ = v___x_1345_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_c_1334_);
v___x_1367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_MessageData_ofName(v_mod_1350_);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_MessageData_note(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_msg_1317_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1374_);
v___x_1376_ = v___x_1345_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1379_; 
lean_dec_ref(v_env_1322_);
lean_dec(v_declHint_1318_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_msg_1317_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1380_, lean_object* v_declHint_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1380_, v_declHint_1381_, v___y_1382_);
lean_dec(v___y_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object* v_msg_1385_, lean_object* v_declHint_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v___x_1392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1385_, v_declHint_1386_, v___y_1390_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1397_ = l_Lean_unknownIdentifierMessageTag;
v___x_1398_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_a_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object* v_msg_1403_, lean_object* v_declHint_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1403_, v_declHint_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object* v_msgData_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_env_1418_; lean_object* v___x_1419_; lean_object* v_mctx_1420_; lean_object* v_lctx_1421_; lean_object* v_options_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1417_ = lean_st_ref_get(v___y_1415_);
v_env_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1418_);
lean_dec(v___x_1417_);
v___x_1419_ = lean_st_ref_get(v___y_1413_);
v_mctx_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_mctx_1420_);
lean_dec(v___x_1419_);
v_lctx_1421_ = lean_ctor_get(v___y_1412_, 2);
v_options_1422_ = lean_ctor_get(v___y_1414_, 2);
lean_inc_ref(v_options_1422_);
lean_inc_ref(v_lctx_1421_);
v___x_1423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1423_, 0, v_env_1418_);
lean_ctor_set(v___x_1423_, 1, v_mctx_1420_);
lean_ctor_set(v___x_1423_, 2, v_lctx_1421_);
lean_ctor_set(v___x_1423_, 3, v_options_1422_);
v___x_1424_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_msgData_1411_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object* v_msgData_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object* v_msg_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_ref_1439_; lean_object* v___x_1440_; lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_ref_1439_ = lean_ctor_get(v___y_1436_, 5);
v___x_1440_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msg_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_inc(v_ref_1439_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_ref_1439_);
lean_ctor_set(v___x_1445_, 1, v_a_1441_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 1);
lean_ctor_set(v___x_1443_, 0, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object* v_ref_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_fileName_1464_; lean_object* v_fileMap_1465_; lean_object* v_options_1466_; lean_object* v_currRecDepth_1467_; lean_object* v_maxRecDepth_1468_; lean_object* v_ref_1469_; lean_object* v_currNamespace_1470_; lean_object* v_openDecls_1471_; lean_object* v_initHeartbeats_1472_; lean_object* v_maxHeartbeats_1473_; lean_object* v_quotContext_1474_; lean_object* v_currMacroScope_1475_; uint8_t v_diag_1476_; lean_object* v_cancelTk_x3f_1477_; uint8_t v_suppressElabErrors_1478_; lean_object* v_inheritedTraceOptions_1479_; lean_object* v_ref_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_fileName_1464_ = lean_ctor_get(v___y_1461_, 0);
v_fileMap_1465_ = lean_ctor_get(v___y_1461_, 1);
v_options_1466_ = lean_ctor_get(v___y_1461_, 2);
v_currRecDepth_1467_ = lean_ctor_get(v___y_1461_, 3);
v_maxRecDepth_1468_ = lean_ctor_get(v___y_1461_, 4);
v_ref_1469_ = lean_ctor_get(v___y_1461_, 5);
v_currNamespace_1470_ = lean_ctor_get(v___y_1461_, 6);
v_openDecls_1471_ = lean_ctor_get(v___y_1461_, 7);
v_initHeartbeats_1472_ = lean_ctor_get(v___y_1461_, 8);
v_maxHeartbeats_1473_ = lean_ctor_get(v___y_1461_, 9);
v_quotContext_1474_ = lean_ctor_get(v___y_1461_, 10);
v_currMacroScope_1475_ = lean_ctor_get(v___y_1461_, 11);
v_diag_1476_ = lean_ctor_get_uint8(v___y_1461_, sizeof(void*)*14);
v_cancelTk_x3f_1477_ = lean_ctor_get(v___y_1461_, 12);
v_suppressElabErrors_1478_ = lean_ctor_get_uint8(v___y_1461_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1479_ = lean_ctor_get(v___y_1461_, 13);
v_ref_1480_ = l_Lean_replaceRef(v_ref_1457_, v_ref_1469_);
lean_inc_ref(v_inheritedTraceOptions_1479_);
lean_inc(v_cancelTk_x3f_1477_);
lean_inc(v_currMacroScope_1475_);
lean_inc(v_quotContext_1474_);
lean_inc(v_maxHeartbeats_1473_);
lean_inc(v_initHeartbeats_1472_);
lean_inc(v_openDecls_1471_);
lean_inc(v_currNamespace_1470_);
lean_inc(v_maxRecDepth_1468_);
lean_inc(v_currRecDepth_1467_);
lean_inc_ref(v_options_1466_);
lean_inc_ref(v_fileMap_1465_);
lean_inc_ref(v_fileName_1464_);
v___x_1481_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1481_, 0, v_fileName_1464_);
lean_ctor_set(v___x_1481_, 1, v_fileMap_1465_);
lean_ctor_set(v___x_1481_, 2, v_options_1466_);
lean_ctor_set(v___x_1481_, 3, v_currRecDepth_1467_);
lean_ctor_set(v___x_1481_, 4, v_maxRecDepth_1468_);
lean_ctor_set(v___x_1481_, 5, v_ref_1480_);
lean_ctor_set(v___x_1481_, 6, v_currNamespace_1470_);
lean_ctor_set(v___x_1481_, 7, v_openDecls_1471_);
lean_ctor_set(v___x_1481_, 8, v_initHeartbeats_1472_);
lean_ctor_set(v___x_1481_, 9, v_maxHeartbeats_1473_);
lean_ctor_set(v___x_1481_, 10, v_quotContext_1474_);
lean_ctor_set(v___x_1481_, 11, v_currMacroScope_1475_);
lean_ctor_set(v___x_1481_, 12, v_cancelTk_x3f_1477_);
lean_ctor_set(v___x_1481_, 13, v_inheritedTraceOptions_1479_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*14, v_diag_1476_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*14 + 1, v_suppressElabErrors_1478_);
v___x_1482_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1458_, v___y_1459_, v___y_1460_, v___x_1481_, v___y_1462_);
lean_dec_ref(v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1483_, lean_object* v_msg_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1483_, v_msg_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_ref_1483_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_ref_1491_, lean_object* v_msg_1492_, lean_object* v_declHint_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v___x_1501_; 
v___x_1499_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1492_, v_declHint_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1491_, v_a_1500_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1502_, lean_object* v_msg_1503_, lean_object* v_declHint_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1502_, v_msg_1503_, v_declHint_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_ref_1502_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1514_, lean_object* v_constName_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1521_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1522_ = 0;
lean_inc(v_constName_1515_);
v___x_1523_ = l_Lean_MessageData_ofConstName(v_constName_1515_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1514_, v___x_1526_, v_constName_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1528_, lean_object* v_constName_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1528_, v_constName_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_ref_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object* v_constName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_ref_1542_; lean_object* v___x_1543_; 
v_ref_1542_ = lean_ctor_get(v___y_1539_, 5);
v___x_1543_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1542_, v_constName_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object* v_constName_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v_env_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_st_ref_get(v___y_1555_);
v_env_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_ref(v_env_1558_);
lean_dec(v___x_1557_);
v___x_1559_ = 0;
lean_inc(v_constName_1551_);
v___x_1560_ = l_Lean_Environment_find_x3f(v_env_1558_, v_constName_1551_, v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1561_;
}
else
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_constName_1551_);
v_val_1562_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1560_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v___x_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 0);
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_val_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object* v_constName_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_constName_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object* v_mvarId_1583_, lean_object* v_e_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
lean_inc(v_mvarId_1583_);
v___x_1590_ = l_Lean_MVarId_getTag(v_mvarId_1583_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc_ref(v_e_1584_);
v___x_1592_ = lean_infer_type(v_e_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
v___x_1594_ = lean_whnf(v_a_1593_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = l_Lean_Expr_getAppFn(v_a_1595_);
if (lean_obj_tag(v___x_1596_) == 4)
{
lean_object* v_declName_1597_; lean_object* v___x_1598_; 
v_declName_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_n(v_declName_1597_, 2);
lean_dec_ref(v___x_1596_);
v___x_1598_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_declName_1597_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
if (lean_obj_tag(v_a_1599_) == 5)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v_a_1599_);
v___x_1600_ = l_Lean_mkCasesOnName(v_declName_1597_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l_Lean_Meta_mkRecursorInfo(v___x_1600_, v___x_1601_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = l_Lean_Meta_RecursorInfo_numIndices(v_a_1603_);
v___x_1606_ = lean_nat_dec_lt(v___x_1604_, v___x_1605_);
lean_dec(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_inc_ref(v_e_1584_);
v___x_1607_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v_mvarId_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___x_1631_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1607_);
v___x_1631_ = lean_unbox(v_a_1608_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_inc_ref(v_e_1584_);
v___x_1632_ = l_Lean_Meta_isProof(v_e_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; uint8_t v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = lean_unbox(v_a_1633_);
lean_dec(v_a_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1636_ = l_Lean_Core_mkFreshUserName(v___x_1635_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__3));
v___x_1639_ = l_Lean_MVarId_assertExt(v_mvarId_1583_, v_a_1637_, v_a_1595_, v_e_1584_, v___x_1638_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v_mvarId_1610_ = v_a_1640_;
v___y_1611_ = v___y_1585_;
v___y_1612_ = v___y_1586_;
v___y_1613_ = v___y_1587_;
v___y_1614_ = v___y_1588_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1603_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
v_a_1641_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1639_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1639_);
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
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1603_);
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1649_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1636_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1636_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1658_ = l_Lean_Core_mkFreshUserName(v___x_1657_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_Lean_MVarId_assert(v_mvarId_1583_, v_a_1659_, v_a_1595_, v_e_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1660_);
v_mvarId_1610_ = v_a_1661_;
v___y_1611_ = v___y_1585_;
v___y_1612_ = v___y_1586_;
v___y_1613_ = v___y_1587_;
v___y_1614_ = v___y_1588_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1603_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
v_a_1662_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1603_);
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1603_);
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1678_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1632_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1632_);
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
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1595_);
v___x_1686_ = l_Lean_Expr_fvarId_x21(v_e_1584_);
lean_dec_ref(v_e_1584_);
v___x_1687_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1688_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1603_, v_a_1591_, v_mvarId_1583_, v___x_1686_, v___x_1687_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v___x_1688_;
}
v___jp_1609_:
{
uint8_t v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
v___x_1616_ = l_Lean_Meta_intro1Core(v_mvarId_1610_, v___x_1615_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v_fst_1618_ = lean_ctor_get(v_a_1617_, 0);
lean_inc(v_fst_1618_);
v_snd_1619_ = lean_ctor_get(v_a_1617_, 1);
lean_inc_n(v_snd_1619_, 2);
lean_dec(v_a_1617_);
v___x_1620_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1621_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1621_, 0, v_a_1603_);
lean_closure_set(v___x_1621_, 1, v_a_1591_);
lean_closure_set(v___x_1621_, 2, v_snd_1619_);
lean_closure_set(v___x_1621_, 3, v_fst_1618_);
lean_closure_set(v___x_1621_, 4, v___x_1620_);
v___x_1622_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_snd_1619_, v___x_1621_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v___x_1622_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v_a_1603_);
lean_dec(v_a_1591_);
v_a_1623_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1616_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1616_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1603_);
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1689_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1607_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1607_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v___x_1697_; 
lean_dec(v_a_1595_);
v___x_1697_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1583_, v_e_1584_, v___x_1601_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v_mvarId_1699_; lean_object* v_indicesFVarIds_1700_; lean_object* v_fvarId_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1697_);
v_mvarId_1699_ = lean_ctor_get(v_a_1698_, 0);
lean_inc_n(v_mvarId_1699_, 2);
v_indicesFVarIds_1700_ = lean_ctor_get(v_a_1698_, 1);
lean_inc_ref(v_indicesFVarIds_1700_);
v_fvarId_1701_ = lean_ctor_get(v_a_1698_, 2);
lean_inc(v_fvarId_1701_);
lean_dec(v_a_1698_);
v___x_1702_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1702_, 0, v_a_1603_);
lean_closure_set(v___x_1702_, 1, v_a_1591_);
lean_closure_set(v___x_1702_, 2, v_mvarId_1699_);
lean_closure_set(v___x_1702_, 3, v_fvarId_1701_);
lean_closure_set(v___x_1702_, 4, v_indicesFVarIds_1700_);
v___x_1703_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1699_, v___x_1702_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v___x_1703_;
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_a_1603_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
v_a_1704_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1697_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1697_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1712_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1602_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1602_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v___x_1720_; 
lean_dec(v_a_1599_);
lean_dec(v_declName_1597_);
lean_dec(v_a_1591_);
v___x_1720_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1583_, v_e_1584_, v_a_1595_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v___x_1720_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_declName_1597_);
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1721_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1598_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1598_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v___x_1729_; 
lean_dec_ref(v___x_1596_);
lean_dec(v_a_1591_);
v___x_1729_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1583_, v_e_1584_, v_a_1595_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v___x_1729_;
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1730_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1594_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1594_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1591_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1738_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1592_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1592_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_e_1584_);
lean_dec(v_mvarId_1583_);
v_a_1746_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1590_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1590_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object* v_mvarId_1754_, lean_object* v_e_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_Grind_cases___lam__1(v_mvarId_1754_, v_e_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases(lean_object* v_mvarId_1762_, lean_object* v_e_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; 
lean_inc(v_mvarId_1762_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1769_, 0, v_mvarId_1762_);
lean_closure_set(v___f_1769_, 1, v_e_1763_);
v___x_1770_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1762_, v___f_1769_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object* v_mvarId_1771_, lean_object* v_e_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Meta_Grind_cases(v_mvarId_1771_, v_e_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object* v_mvarId_1779_, lean_object* v_val_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1779_, v_val_1780_, v___y_1782_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object* v_mvarId_1787_, lean_object* v_val_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(v_mvarId_1787_, v_val_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object* v_upperBound_1795_, lean_object* v___y_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_a_1799_, lean_object* v_mvarId_1800_, lean_object* v_inst_1801_, lean_object* v_R_1802_, lean_object* v_a_1803_, lean_object* v_b_1804_, lean_object* v_c_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1795_, v___y_1796_, v___x_1797_, v___x_1798_, v_a_1799_, v_mvarId_1800_, v_a_1803_, v_b_1804_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object* v_upperBound_1812_, lean_object* v___y_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v_a_1816_, lean_object* v_mvarId_1817_, lean_object* v_inst_1818_, lean_object* v_R_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_, lean_object* v_c_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(v_upperBound_1812_, v___y_1813_, v___x_1814_, v___x_1815_, v_a_1816_, v_mvarId_1817_, v_inst_1818_, v_R_1819_, v_a_1820_, v_b_1821_, v_c_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___x_1815_);
lean_dec(v_upperBound_1812_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object* v_00_u03b1_1829_, lean_object* v_constName_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_constName_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(v_00_u03b1_1837_, v_constName_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_x_1846_, v_x_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1850_, lean_object* v_ref_1851_, lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1851_, v_constName_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_ref_1860_, lean_object* v_constName_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(v_00_u03b1_1859_, v_ref_1860_, v_constName_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v_ref_1860_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1868_, lean_object* v_x_1869_, size_t v_x_1870_, size_t v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1869_, v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
size_t v_x_13905__boxed_1881_; size_t v_x_13906__boxed_1882_; lean_object* v_res_1883_; 
v_x_13905__boxed_1881_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_x_13906__boxed_1882_ = lean_unbox_usize(v_x_1878_);
lean_dec(v_x_1878_);
v_res_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(v_00_u03b2_1875_, v_x_1876_, v_x_13905__boxed_1881_, v_x_13906__boxed_1882_, v_x_1879_, v_x_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_1884_, lean_object* v_ref_1885_, lean_object* v_msg_1886_, lean_object* v_declHint_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1885_, v_msg_1886_, v_declHint_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_ref_1895_, lean_object* v_msg_1896_, lean_object* v_declHint_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_1894_, v_ref_1895_, v_msg_1896_, v_declHint_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v_ref_1895_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1904_, lean_object* v_n_1905_, lean_object* v_k_1906_, lean_object* v_v_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v_n_1905_, v_k_1906_, v_v_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object* v_00_u03b2_1909_, size_t v_depth_1910_, lean_object* v_keys_1911_, lean_object* v_vals_1912_, lean_object* v_heq_1913_, lean_object* v_i_1914_, lean_object* v_entries_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_1910_, v_keys_1911_, v_vals_1912_, v_i_1914_, v_entries_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1917_, lean_object* v_depth_1918_, lean_object* v_keys_1919_, lean_object* v_vals_1920_, lean_object* v_heq_1921_, lean_object* v_i_1922_, lean_object* v_entries_1923_){
_start:
{
size_t v_depth_boxed_1924_; lean_object* v_res_1925_; 
v_depth_boxed_1924_ = lean_unbox_usize(v_depth_1918_);
lean_dec(v_depth_1918_);
v_res_1925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(v_00_u03b2_1917_, v_depth_boxed_1924_, v_keys_1919_, v_vals_1920_, v_heq_1921_, v_i_1922_, v_entries_1923_);
lean_dec_ref(v_vals_1920_);
lean_dec_ref(v_keys_1919_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object* v_msg_1926_, lean_object* v_declHint_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1926_, v_declHint_1927_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_1934_, lean_object* v_declHint_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_1934_, v_declHint_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object* v_00_u03b1_1942_, lean_object* v_ref_1943_, lean_object* v_msg_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1943_, v_msg_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_ref_1952_, lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_1951_, v_ref_1952_, v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v_ref_1952_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_x_1961_, v_x_1962_, v_x_1963_, v_x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1966_, lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_1974_, v_msg_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases = _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
}
#ifdef __cplusplus
}
#endif

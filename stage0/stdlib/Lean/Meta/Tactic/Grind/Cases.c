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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(lean_object* v_x_66_, size_t v_x_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_es_69_; lean_object* v___x_70_; size_t v___x_71_; size_t v___x_72_; lean_object* v_j_73_; lean_object* v___x_74_; 
v_es_69_ = lean_ctor_get(v_x_66_, 0);
v___x_70_ = lean_box(2);
v___x_71_ = ((size_t)31ULL);
v___x_72_ = lean_usize_land(v_x_67_, v___x_71_);
v_j_73_ = lean_usize_to_nat(v___x_72_);
v___x_74_ = lean_array_get_borrowed(v___x_70_, v_es_69_, v_j_73_);
lean_dec(v_j_73_);
switch(lean_obj_tag(v___x_74_))
{
case 0:
{
lean_object* v_key_75_; uint8_t v___x_76_; 
v_key_75_ = lean_ctor_get(v___x_74_, 0);
v___x_76_ = lean_name_eq(v_x_68_, v_key_75_);
return v___x_76_;
}
case 1:
{
lean_object* v_node_77_; size_t v___x_78_; size_t v___x_79_; 
v_node_77_ = lean_ctor_get(v___x_74_, 0);
v___x_78_ = ((size_t)5ULL);
v___x_79_ = lean_usize_shift_right(v_x_67_, v___x_78_);
v_x_66_ = v_node_77_;
v_x_67_ = v___x_79_;
goto _start;
}
default: 
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
else
{
lean_object* v_ks_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_ks_82_ = lean_ctor_get(v_x_66_, 0);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_ks_82_, v___x_83_, v_x_68_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
size_t v_x_122__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_122__boxed_88_ = lean_unbox_usize(v_x_86_);
lean_dec(v_x_86_);
v_res_89_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_85_, v_x_122__boxed_88_, v_x_87_);
lean_dec(v_x_87_);
lean_dec_ref(v_x_85_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint64_t v___y_94_; 
if (lean_obj_tag(v_x_92_) == 0)
{
uint64_t v___x_97_; 
v___x_97_ = 1723ULL;
v___y_94_ = v___x_97_;
goto v___jp_93_;
}
else
{
uint64_t v_hash_98_; 
v_hash_98_ = lean_ctor_get_uint64(v_x_92_, sizeof(void*)*2);
v___y_94_ = v_hash_98_;
goto v___jp_93_;
}
v___jp_93_:
{
size_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_uint64_to_usize(v___y_94_);
v___x_96_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_91_, v___x_95_, v_x_92_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec_ref(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object* v_s_103_, lean_object* v_declName_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_103_, v_declName_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_contains___boxed(lean_object* v_s_106_, lean_object* v_declName_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_106_, v_declName_107_);
lean_dec(v_declName_107_);
lean_dec_ref(v_s_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(lean_object* v_00_u03b2_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(lean_object* v_00_u03b2_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(v_00_u03b2_114_, v_x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec_ref(v_x_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(lean_object* v_00_u03b2_119_, lean_object* v_x_120_, size_t v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_120_, v_x_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
size_t v_x_189__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_x_189__boxed_128_ = lean_unbox_usize(v_x_126_);
lean_dec(v_x_126_);
v_res_129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(v_00_u03b2_124_, v_x_125_, v_x_189__boxed_128_, v_x_127_);
lean_dec(v_x_127_);
lean_dec_ref(v_x_125_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_131_, lean_object* v_keys_132_, lean_object* v_vals_133_, lean_object* v_heq_134_, lean_object* v_i_135_, lean_object* v_k_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_132_, v_i_135_, v_k_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_138_, lean_object* v_keys_139_, lean_object* v_vals_140_, lean_object* v_heq_141_, lean_object* v_i_142_, lean_object* v_k_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(v_00_u03b2_138_, v_keys_139_, v_vals_140_, v_heq_141_, v_i_142_, v_k_143_);
lean_dec(v_k_143_);
lean_dec_ref(v_vals_140_);
lean_dec_ref(v_keys_139_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_146_, lean_object* v_v_147_, lean_object* v_i_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_get_size(v_xs_146_);
v___x_150_ = lean_nat_dec_lt(v_i_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_i_148_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_array_fget_borrowed(v_xs_146_, v_i_148_);
v___x_153_ = lean_name_eq(v___x_152_, v_v_147_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_i_148_, v___x_154_);
lean_dec(v_i_148_);
v_i_148_ = v___x_155_;
goto _start;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_i_148_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_158_, lean_object* v_v_159_, lean_object* v_i_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_158_, v_v_159_, v_i_160_);
lean_dec(v_v_159_);
lean_dec_ref(v_xs_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(lean_object* v_xs_162_, lean_object* v_v_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_162_, v_v_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_166_, lean_object* v_v_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_xs_166_, v_v_167_);
lean_dec(v_v_167_);
lean_dec_ref(v_xs_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(lean_object* v_x_169_, size_t v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_es_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v_j_176_; lean_object* v_entry_177_; 
v_es_172_ = lean_ctor_get(v_x_169_, 0);
v___x_173_ = lean_box(2);
v___x_174_ = ((size_t)31ULL);
v___x_175_ = lean_usize_land(v_x_170_, v___x_174_);
v_j_176_ = lean_usize_to_nat(v___x_175_);
v_entry_177_ = lean_array_get(v___x_173_, v_es_172_, v_j_176_);
switch(lean_obj_tag(v_entry_177_))
{
case 0:
{
lean_object* v_key_178_; uint8_t v___x_179_; 
v_key_178_ = lean_ctor_get(v_entry_177_, 0);
lean_inc(v_key_178_);
lean_dec_ref_known(v_entry_177_, 2);
v___x_179_ = lean_name_eq(v_x_171_, v_key_178_);
lean_dec(v_key_178_);
if (v___x_179_ == 0)
{
lean_dec(v_j_176_);
return v_x_169_;
}
else
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
lean_inc_ref(v_es_172_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_x_169_, 0);
lean_dec(v_unused_188_);
v___x_181_ = v_x_169_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_array_set(v_es_172_, v_j_176_, v___x_173_);
lean_dec(v_j_176_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
case 1:
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_223_; 
lean_inc_ref(v_es_172_);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v_x_169_, 0);
lean_dec(v_unused_224_);
v___x_190_ = v_x_169_;
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_x_169_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_223_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_node_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_222_; 
v_node_192_ = lean_ctor_get(v_entry_177_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_entry_177_);
if (v_isSharedCheck_222_ == 0)
{
v___x_194_ = v_entry_177_;
v_isShared_195_ = v_isSharedCheck_222_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_node_192_);
lean_dec(v_entry_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_222_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
size_t v___x_196_; lean_object* v_entries_197_; size_t v___x_198_; lean_object* v_newNode_199_; lean_object* v___x_200_; 
v___x_196_ = ((size_t)5ULL);
v_entries_197_ = lean_array_set(v_es_172_, v_j_176_, v___x_173_);
v___x_198_ = lean_usize_shift_right(v_x_170_, v___x_196_);
v_newNode_199_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_node_192_, v___x_198_, v_x_171_);
lean_inc_ref(v_newNode_199_);
v___x_200_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_202_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_newNode_199_);
v___x_202_ = v___x_194_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_newNode_199_);
v___x_202_ = v_reuseFailAlloc_207_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_array_set(v_entries_197_, v_j_176_, v___x_202_);
lean_dec(v_j_176_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_203_);
v___x_205_ = v___x_190_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_val_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_newNode_199_);
lean_del_object(v___x_194_);
v_val_208_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_200_, 1);
v_fst_209_ = lean_ctor_get(v_val_208_, 0);
v_snd_210_ = lean_ctor_get(v_val_208_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_val_208_);
if (v_isSharedCheck_221_ == 0)
{
v___x_212_ = v_val_208_;
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snd_210_);
lean_inc(v_fst_209_);
lean_dec(v_val_208_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_210_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_array_set(v_entries_197_, v_j_176_, v___x_215_);
lean_dec(v_j_176_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_216_);
v___x_218_ = v___x_190_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_176_);
return v_x_169_;
}
}
}
else
{
lean_object* v_ks_225_; lean_object* v_vs_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_ks_225_ = lean_ctor_get(v_x_169_, 0);
v_vs_226_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_240_ == 0)
{
v___x_228_ = v_x_169_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_vs_226_);
lean_inc(v_ks_225_);
lean_dec(v_x_169_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; 
v___x_230_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_ks_225_, v_x_171_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_232_; 
if (v_isShared_229_ == 0)
{
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_ks_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_vs_226_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v_val_234_; lean_object* v_keys_x27_235_; lean_object* v_vals_x27_236_; lean_object* v___x_238_; 
v_val_234_ = lean_ctor_get(v___x_230_, 0);
lean_inc_n(v_val_234_, 2);
lean_dec_ref_known(v___x_230_, 1);
v_keys_x27_235_ = l_Array_eraseIdx___redArg(v_ks_225_, v_val_234_);
v_vals_x27_236_ = l_Array_eraseIdx___redArg(v_vs_226_, v_val_234_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v_vals_x27_236_);
lean_ctor_set(v___x_228_, 0, v_keys_x27_235_);
v___x_238_ = v___x_228_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_keys_x27_235_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_vals_x27_236_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_173__boxed_244_; lean_object* v_res_245_; 
v_x_173__boxed_244_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_res_245_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_241_, v_x_173__boxed_244_, v_x_243_);
lean_dec(v_x_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
uint64_t v___y_249_; 
if (lean_obj_tag(v_x_247_) == 0)
{
uint64_t v___x_252_; 
v___x_252_ = 1723ULL;
v___y_249_ = v___x_252_;
goto v___jp_248_;
}
else
{
uint64_t v_hash_253_; 
v_hash_253_ = lean_ctor_get_uint64(v_x_247_, sizeof(void*)*2);
v___y_249_ = v_hash_253_;
goto v___jp_248_;
}
v___jp_248_:
{
size_t v_h_250_; lean_object* v___x_251_; 
v_h_250_ = lean_uint64_to_usize(v___y_249_);
v___x_251_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_246_, v_h_250_, v_x_247_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_254_, v_x_255_);
lean_dec(v_x_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object* v_s_257_, lean_object* v_declName_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_257_, v_declName_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_erase___boxed(lean_object* v_s_260_, lean_object* v_declName_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Grind_CasesTypes_erase(v_s_260_, v_declName_261_);
lean_dec(v_declName_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(lean_object* v_00_u03b2_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(lean_object* v_00_u03b2_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(v_00_u03b2_267_, v_x_268_, v_x_269_);
lean_dec(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(lean_object* v_00_u03b2_271_, lean_object* v_x_272_, size_t v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_272_, v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
size_t v_x_333__boxed_280_; lean_object* v_res_281_; 
v_x_333__boxed_280_ = lean_unbox_usize(v_x_278_);
lean_dec(v_x_278_);
v_res_281_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(v_00_u03b2_276_, v_x_277_, v_x_333__boxed_280_, v_x_279_);
lean_dec(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_282_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_i_284_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_k_x27_289_; uint8_t v___x_290_; 
v_k_x27_289_ = lean_array_fget_borrowed(v_keys_282_, v_i_284_);
v___x_290_ = lean_name_eq(v_k_285_, v_k_x27_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_i_284_, v___x_291_);
lean_dec(v_i_284_);
v_i_284_ = v___x_292_;
goto _start;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_array_fget_borrowed(v_vals_283_, v_i_284_);
lean_dec(v_i_284_);
lean_inc(v___x_294_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_296_, lean_object* v_vals_297_, lean_object* v_i_298_, lean_object* v_k_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_296_, v_vals_297_, v_i_298_, v_k_299_);
lean_dec(v_k_299_);
lean_dec_ref(v_vals_297_);
lean_dec_ref(v_keys_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_301_, size_t v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_es_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v_j_308_; lean_object* v___x_309_; 
v_es_304_ = lean_ctor_get(v_x_301_, 0);
v___x_305_ = lean_box(2);
v___x_306_ = ((size_t)31ULL);
v___x_307_ = lean_usize_land(v_x_302_, v___x_306_);
v_j_308_ = lean_usize_to_nat(v___x_307_);
v___x_309_ = lean_array_get_borrowed(v___x_305_, v_es_304_, v_j_308_);
lean_dec(v_j_308_);
switch(lean_obj_tag(v___x_309_))
{
case 0:
{
lean_object* v_key_310_; lean_object* v_val_311_; uint8_t v___x_312_; 
v_key_310_ = lean_ctor_get(v___x_309_, 0);
v_val_311_ = lean_ctor_get(v___x_309_, 1);
v___x_312_ = lean_name_eq(v_x_303_, v_key_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_inc(v_val_311_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_val_311_);
return v___x_314_;
}
}
case 1:
{
lean_object* v_node_315_; size_t v___x_316_; size_t v___x_317_; 
v_node_315_ = lean_ctor_get(v___x_309_, 0);
v___x_316_ = ((size_t)5ULL);
v___x_317_ = lean_usize_shift_right(v_x_302_, v___x_316_);
v_x_301_ = v_node_315_;
v_x_302_ = v___x_317_;
goto _start;
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
}
}
else
{
lean_object* v_ks_320_; lean_object* v_vs_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_ks_320_ = lean_ctor_get(v_x_301_, 0);
v_vs_321_ = lean_ctor_get(v_x_301_, 1);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_320_, v_vs_321_, v___x_322_, v_x_303_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
size_t v_x_136__boxed_327_; lean_object* v_res_328_; 
v_x_136__boxed_327_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_res_328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_324_, v_x_136__boxed_327_, v_x_326_);
lean_dec(v_x_326_);
lean_dec_ref(v_x_324_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint64_t v___y_332_; 
if (lean_obj_tag(v_x_330_) == 0)
{
uint64_t v___x_335_; 
v___x_335_ = 1723ULL;
v___y_332_ = v___x_335_;
goto v___jp_331_;
}
else
{
uint64_t v_hash_336_; 
v_hash_336_ = lean_ctor_get_uint64(v_x_330_, sizeof(void*)*2);
v___y_332_ = v_hash_336_;
goto v___jp_331_;
}
v___jp_331_:
{
size_t v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_uint64_to_usize(v___y_332_);
v___x_334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_329_, v___x_333_, v_x_330_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_x_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f(lean_object* v_s_340_, lean_object* v_declName_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_340_, v_declName_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(lean_object* v_s_343_, lean_object* v_declName_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Grind_CasesTypes_find_x3f(v_s_343_, v_declName_344_);
lean_dec(v_declName_344_);
lean_dec_ref(v_s_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(v_00_u03b2_350_, v_x_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec_ref(v_x_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_355_, v_x_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_209__boxed_363_; lean_object* v_res_364_; 
v_x_209__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(v_00_u03b2_359_, v_x_360_, v_x_209__boxed_363_, v_x_362_);
lean_dec(v_x_362_);
lean_dec_ref(v_x_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_heq_368_, lean_object* v_i_369_, lean_object* v_k_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_366_, v_vals_367_, v_i_369_, v_k_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_heq_375_, lean_object* v_i_376_, lean_object* v_k_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_372_, v_keys_373_, v_vals_374_, v_heq_375_, v_i_376_, v_k_377_);
lean_dec(v_k_377_);
lean_dec_ref(v_vals_374_);
lean_dec_ref(v_keys_373_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object* v_s_379_, lean_object* v_declName_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_379_, v_declName_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_380_);
return v___x_382_;
}
else
{
lean_object* v_val_383_; uint8_t v___x_384_; 
v_val_383_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_381_, 1);
v___x_384_ = lean_unbox(v_val_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
lean_dec(v_val_383_);
v___x_385_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_380_);
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_val_383_);
lean_dec(v_val_383_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(lean_object* v_s_387_, lean_object* v_declName_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_387_, v_declName_388_);
lean_dec(v_declName_388_);
lean_dec_ref(v_s_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object* v_s_391_, lean_object* v_declName_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_391_, v_declName_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_392_);
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = 1;
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(lean_object* v_s_396_, lean_object* v_declName_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_396_, v_declName_397_);
lean_dec(v_declName_397_);
lean_dec_ref(v_s_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(lean_object* v_declName_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_env_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_403_);
v___x_405_ = l_Lean_isInductiveCore_x3f(v_env_404_, v_declName_400_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(lean_object* v_declName_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(lean_object* v_declName_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_411_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(lean_object* v_declName_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(v_declName_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object* v_declName_421_, uint8_t v_eager_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_448_; 
lean_inc(v_declName_421_);
v___x_426_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_421_, v_a_424_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_448_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_448_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
if (lean_obj_tag(v_a_427_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v_val_436_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_445_ == 0)
{
v___x_438_ = v_a_427_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v_a_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v_isRec_440_; 
v_isRec_440_ = lean_ctor_get_uint8(v_val_436_, sizeof(void*)*6);
lean_dec(v_val_436_);
if (v_isRec_440_ == 0)
{
lean_del_object(v___x_438_);
goto v___jp_431_;
}
else
{
if (v_eager_422_ == 0)
{
lean_del_object(v___x_438_);
goto v___jp_431_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_del_object(v___x_429_);
lean_dec(v_declName_421_);
v___x_441_ = lean_box(0);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_del_object(v___x_429_);
lean_dec(v_a_427_);
lean_dec(v_declName_421_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
v___jp_431_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_declName_421_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(lean_object* v_declName_449_, lean_object* v_eager_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
uint8_t v_eager_boxed_454_; lean_object* v_res_455_; 
v_eager_boxed_454_ = lean_unbox(v_eager_450_);
v_res_455_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_449_, v_eager_boxed_454_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object* v_declName_456_, uint8_t v_eager_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_456_, v_eager_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
if (lean_obj_tag(v_a_462_) == 0)
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = 0;
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
else
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec_ref_known(v_a_462_, 1);
v___x_471_ = 1;
v___x_472_ = lean_box(v___x_471_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_472_);
v___x_474_ = v___x_464_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_461_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_461_);
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
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(lean_object* v_declName_485_, lean_object* v_eager_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
uint8_t v_eager_boxed_490_; lean_object* v_res_491_; 
v_eager_boxed_490_ = lean_unbox(v_eager_486_);
v_res_491_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_485_, v_eager_boxed_490_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object* v_declName_492_, uint8_t v_eager_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_492_, v_eager_493_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
if (lean_obj_tag(v_a_500_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_505_; 
lean_del_object(v___x_502_);
v_val_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v_a_500_, 1);
v___x_505_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_504_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_a_500_);
v___x_506_ = lean_box(0);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_499_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(lean_object* v_declName_519_, lean_object* v_eager_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
uint8_t v_eager_boxed_526_; lean_object* v_res_527_; 
v_eager_boxed_526_ = lean_unbox(v_eager_520_);
v_res_527_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_519_, v_eager_boxed_526_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_528_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_ctor_set(v___x_533_, 3, v___x_532_);
lean_ctor_set(v___x_533_, 4, v___x_531_);
lean_ctor_set(v___x_533_, 5, v___x_531_);
lean_ctor_set(v___x_533_, 6, v___x_531_);
lean_ctor_set(v___x_533_, 7, v___x_531_);
lean_ctor_set(v___x_533_, 8, v___x_531_);
lean_ctor_set(v___x_533_, 9, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_unsigned_to_nat(32u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = ((size_t)5ULL);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_unsigned_to_nat(32u);
v___x_540_ = lean_mk_empty_array_with_capacity(v___x_539_);
v___x_541_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3);
v___x_542_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_538_);
lean_ctor_set(v___x_542_, 3, v___x_538_);
lean_ctor_set_usize(v___x_542_, 4, v___x_537_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_543_ = lean_box(1);
v___x_544_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4);
v___x_545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_543_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(lean_object* v_msgData_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_options_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_551_ = lean_st_ref_get(v___y_549_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc_ref(v_env_552_);
lean_dec(v___x_551_);
v_options_553_ = lean_ctor_get(v___y_548_, 2);
v___x_554_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_555_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_553_);
v___x_556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_556_, 0, v_env_552_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
lean_ctor_set(v___x_556_, 3, v_options_553_);
v___x_557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_msgData_547_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(lean_object* v_msgData_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_ref_568_; lean_object* v___x_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v_ref_568_ = lean_ctor_get(v___y_565_, 5);
v___x_569_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msg_564_, v___y_565_, v___y_566_);
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
lean_inc(v_ref_568_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_ref_568_);
lean_ctor_set(v___x_574_, 1, v_a_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 1);
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__4));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_Lean_Meta_Grind_validateCasesAttr___closed__6));
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object* v_declName_596_, uint8_t v_eager_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; 
lean_inc(v_declName_596_);
v___x_601_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_596_, v_eager_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_624_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_624_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_624_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_624_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_unbox(v_a_602_);
if (v___x_606_ == 0)
{
lean_del_object(v___x_604_);
if (v_eager_597_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_a_602_);
v___x_607_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__1, &l_Lean_Meta_Grind_validateCasesAttr___closed__1_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1);
v___x_608_ = l_Lean_MessageData_ofConstName(v_declName_596_, v_eager_597_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__3, &l_Lean_Meta_Grind_validateCasesAttr___closed__3_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_611_, v_a_598_, v_a_599_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_613_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__5, &l_Lean_Meta_Grind_validateCasesAttr___closed__5_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5);
v___x_614_ = lean_unbox(v_a_602_);
lean_dec(v_a_602_);
v___x_615_ = l_Lean_MessageData_ofConstName(v_declName_596_, v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_validateCasesAttr___closed__7, &l_Lean_Meta_Grind_validateCasesAttr___closed__7_once, _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_618_, v_a_598_, v_a_599_);
return v___x_619_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec(v_a_602_);
lean_dec(v_declName_596_);
v___x_620_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_620_);
v___x_622_ = v___x_604_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_declName_596_);
v_a_625_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_601_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_601_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_validateCasesAttr___boxed(lean_object* v_declName_633_, lean_object* v_eager_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
uint8_t v_eager_boxed_638_; lean_object* v_res_639_; 
v_eager_boxed_638_ = lean_unbox(v_eager_634_);
v_res_639_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_633_, v_eager_boxed_638_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v_msg_641_, v___y_642_, v___y_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(v_00_u03b1_646_, v_msg_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object* v_s_652_, lean_object* v_declName_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_652_, v_declName_653_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_s_652_);
v___x_658_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_653_, v_a_654_, v_a_655_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_652_, v_declName_653_);
lean_dec(v_declName_653_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(lean_object* v_s_661_, lean_object* v_declName_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_661_, v_declName_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_666_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object* v_declName_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_673_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_declName_673_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_680_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_681_ = 0;
v___x_682_ = l_Lean_MessageData_ofConstName(v_declName_673_, v___x_681_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_685_, v_a_674_, v_a_675_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(lean_object* v_declName_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(lean_object* v_e_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
if (lean_obj_tag(v_e_692_) == 1)
{
lean_object* v_fvarId_698_; lean_object* v___x_699_; 
v_fvarId_698_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_fvarId_698_);
lean_dec_ref_known(v_e_692_, 1);
v___x_699_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_698_, v_a_693_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_716_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_716_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_716_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_lctx_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_lctx_704_ = lean_ctor_get(v_a_693_, 2);
v___x_705_ = l_Lean_LocalDecl_index(v_a_700_);
lean_inc_ref(v_lctx_704_);
v___x_706_ = lean_local_ctx_num_indices(v_lctx_704_);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_sub(v___x_706_, v___x_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_nat_dec_eq(v___x_705_, v___x_708_);
lean_dec(v___x_708_);
lean_dec(v___x_705_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_702_);
v___x_710_ = l_Lean_LocalDecl_type(v_a_700_);
lean_dec(v_a_700_);
v___x_711_ = l_Lean_Meta_isProp(v___x_710_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_a_700_);
v___x_712_ = lean_box(v___x_709_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_712_);
v___x_714_ = v___x_702_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_699_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_699_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_e_692_);
v___x_725_ = 0;
v___x_726_ = lean_box(v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
return v_res_734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(lean_object* v_mvarId_743_, lean_object* v_e_744_, lean_object* v_type_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4);
v___x_753_ = l_Lean_MessageData_ofExpr(v_e_744_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_indentExpr(v_type_745_);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = l_Lean_Meta_throwTacticEx___redArg(v___x_751_, v_mvarId_743_, v___x_757_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(lean_object* v_mvarId_759_, lean_object* v_e_760_, lean_object* v_type_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_759_, v_e_760_, v_type_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(lean_object* v_mvarId_768_, lean_object* v_e_769_, lean_object* v_00_u03b1_770_, lean_object* v_type_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_768_, v_e_769_, v_type_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(lean_object* v_mvarId_778_, lean_object* v_e_779_, lean_object* v_00_u03b1_780_, lean_object* v_type_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(v_mvarId_778_, v_e_779_, v_00_u03b1_780_, v_type_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(lean_object* v_mvarId_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_795_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_795_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(lean_object* v_mvarId_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(lean_object* v_00_u03b1_820_, lean_object* v_mvarId_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_821_, v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(lean_object* v_00_u03b1_829_, lean_object* v_mvarId_830_, lean_object* v_x_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(v_00_u03b1_829_, v_mvarId_830_, v_x_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(lean_object* v_as_838_, size_t v_i_839_, size_t v_stop_840_, lean_object* v_b_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = lean_usize_dec_eq(v_i_839_, v_stop_840_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; size_t v___x_846_; size_t v___x_847_; 
v___x_843_ = 1;
v___x_844_ = lean_array_uget_borrowed(v_as_838_, v_i_839_);
lean_inc(v___x_844_);
v___x_845_ = l_Lean_LocalContext_setKind(v_b_841_, v___x_844_, v___x_843_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_839_, v___x_846_);
v_i_839_ = v___x_847_;
v_b_841_ = v___x_845_;
goto _start;
}
else
{
return v_b_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(lean_object* v_as_849_, lean_object* v_i_850_, lean_object* v_stop_851_, lean_object* v_b_852_){
_start:
{
size_t v_i_boxed_853_; size_t v_stop_boxed_854_; lean_object* v_res_855_; 
v_i_boxed_853_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_stop_boxed_854_ = lean_unbox_usize(v_stop_851_);
lean_dec(v_stop_851_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_849_, v_i_boxed_853_, v_stop_boxed_854_, v_b_852_);
lean_dec_ref(v_as_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_ks_860_; lean_object* v_vs_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_885_; 
v_ks_860_ = lean_ctor_get(v_x_856_, 0);
v_vs_861_ = lean_ctor_get(v_x_856_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_885_ == 0)
{
v___x_863_ = v_x_856_;
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_vs_861_);
lean_inc(v_ks_860_);
lean_dec(v_x_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v_ks_860_);
v___x_866_ = lean_nat_dec_lt(v_x_857_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v_x_857_);
v___x_867_ = lean_array_push(v_ks_860_, v_x_858_);
v___x_868_ = lean_array_push(v_vs_861_, v_x_859_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_868_);
lean_ctor_set(v___x_863_, 0, v___x_867_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v_k_x27_872_; uint8_t v___x_873_; 
v_k_x27_872_ = lean_array_fget_borrowed(v_ks_860_, v_x_857_);
v___x_873_ = l_Lean_instBEqMVarId_beq(v_x_858_, v_k_x27_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_875_; 
if (v_isShared_864_ == 0)
{
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_ks_860_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_vs_861_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_nat_add(v_x_857_, v___x_876_);
lean_dec(v_x_857_);
v_x_856_ = v___x_875_;
v_x_857_ = v___x_877_;
goto _start;
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = lean_array_fset(v_ks_860_, v_x_857_, v_x_858_);
v___x_881_ = lean_array_fset(v_vs_861_, v_x_857_, v_x_859_);
lean_dec(v_x_857_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_881_);
lean_ctor_set(v___x_863_, 0, v___x_880_);
v___x_883_ = v___x_863_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(lean_object* v_n_886_, lean_object* v_k_887_, lean_object* v_v_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_n_886_, v___x_889_, v_k_887_, v_v_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(lean_object* v_x_892_, size_t v_x_893_, size_t v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_object* v_es_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v_j_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_es_897_ = lean_ctor_get(v_x_892_, 0);
v___x_898_ = ((size_t)31ULL);
v___x_899_ = lean_usize_land(v_x_893_, v___x_898_);
v_j_900_ = lean_usize_to_nat(v___x_899_);
v___x_901_ = lean_array_get_size(v_es_897_);
v___x_902_ = lean_nat_dec_lt(v_j_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec(v_j_900_);
lean_dec(v_x_896_);
lean_dec(v_x_895_);
return v_x_892_;
}
else
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_941_; 
lean_inc_ref(v_es_897_);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_x_892_, 0);
lean_dec(v_unused_942_);
v___x_904_ = v_x_892_;
v_isShared_905_ = v_isSharedCheck_941_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_x_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_941_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_v_906_; lean_object* v___x_907_; lean_object* v_xs_x27_908_; lean_object* v___y_910_; 
v_v_906_ = lean_array_fget(v_es_897_, v_j_900_);
v___x_907_ = lean_box(0);
v_xs_x27_908_ = lean_array_fset(v_es_897_, v_j_900_, v___x_907_);
switch(lean_obj_tag(v_v_906_))
{
case 0:
{
lean_object* v_key_915_; lean_object* v_val_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_key_915_ = lean_ctor_get(v_v_906_, 0);
v_val_916_ = lean_ctor_get(v_v_906_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_v_906_);
if (v_isSharedCheck_926_ == 0)
{
v___x_918_ = v_v_906_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_val_916_);
lean_inc(v_key_915_);
lean_dec(v_v_906_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_instBEqMVarId_beq(v_x_895_, v_key_915_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_918_);
v___x_921_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_915_, v_val_916_, v_x_895_, v_x_896_);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___y_910_ = v___x_922_;
goto v___jp_909_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v_val_916_);
lean_dec(v_key_915_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_x_896_);
lean_ctor_set(v___x_918_, 0, v_x_895_);
v___x_924_ = v___x_918_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_x_895_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_x_896_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v___y_910_ = v___x_924_;
goto v___jp_909_;
}
}
}
}
case 1:
{
lean_object* v_node_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_939_; 
v_node_927_ = lean_ctor_get(v_v_906_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_v_906_);
if (v_isSharedCheck_939_ == 0)
{
v___x_929_ = v_v_906_;
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_node_927_);
lean_dec(v_v_906_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_931_ = ((size_t)5ULL);
v___x_932_ = lean_usize_shift_right(v_x_893_, v___x_931_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_x_894_, v___x_933_);
v___x_935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_node_927_, v___x_932_, v___x_934_, v_x_895_, v_x_896_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_935_);
v___x_937_ = v___x_929_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
v___y_910_ = v___x_937_;
goto v___jp_909_;
}
}
}
default: 
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_x_895_);
lean_ctor_set(v___x_940_, 1, v_x_896_);
v___y_910_ = v___x_940_;
goto v___jp_909_;
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_array_fset(v_xs_x27_908_, v_j_900_, v___y_910_);
lean_dec(v_j_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_911_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_ks_943_; lean_object* v_vs_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_964_; 
v_ks_943_ = lean_ctor_get(v_x_892_, 0);
v_vs_944_ = lean_ctor_get(v_x_892_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_964_ == 0)
{
v___x_946_ = v_x_892_;
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_vs_944_);
lean_inc(v_ks_943_);
lean_dec(v_x_892_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_ks_943_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_vs_944_);
v___x_949_ = v_reuseFailAlloc_963_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v_newNode_950_; uint8_t v___y_952_; size_t v___x_958_; uint8_t v___x_959_; 
v_newNode_950_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v___x_949_, v_x_895_, v_x_896_);
v___x_958_ = ((size_t)7ULL);
v___x_959_ = lean_usize_dec_le(v___x_958_, v_x_894_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_960_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_950_);
v___x_961_ = lean_unsigned_to_nat(4u);
v___x_962_ = lean_nat_dec_lt(v___x_960_, v___x_961_);
lean_dec(v___x_960_);
v___y_952_ = v___x_962_;
goto v___jp_951_;
}
else
{
v___y_952_ = v___x_959_;
goto v___jp_951_;
}
v___jp_951_:
{
if (v___y_952_ == 0)
{
lean_object* v_ks_953_; lean_object* v_vs_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_ks_953_ = lean_ctor_get(v_newNode_950_, 0);
lean_inc_ref(v_ks_953_);
v_vs_954_ = lean_ctor_get(v_newNode_950_, 1);
lean_inc_ref(v_vs_954_);
lean_dec_ref(v_newNode_950_);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_x_894_, v_ks_953_, v_vs_954_, v___x_955_, v___x_956_);
lean_dec_ref(v_vs_954_);
lean_dec_ref(v_ks_953_);
return v___x_957_;
}
else
{
return v_newNode_950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(size_t v_depth_965_, lean_object* v_keys_966_, lean_object* v_vals_967_, lean_object* v_i_968_, lean_object* v_entries_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_array_get_size(v_keys_966_);
v___x_971_ = lean_nat_dec_lt(v_i_968_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_i_968_);
return v_entries_969_;
}
else
{
lean_object* v_k_972_; lean_object* v_v_973_; uint64_t v___x_974_; size_t v_h_975_; size_t v___x_976_; lean_object* v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v_h_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_k_972_ = lean_array_fget_borrowed(v_keys_966_, v_i_968_);
v_v_973_ = lean_array_fget_borrowed(v_vals_967_, v_i_968_);
v___x_974_ = l_Lean_instHashableMVarId_hash(v_k_972_);
v_h_975_ = lean_uint64_to_usize(v___x_974_);
v___x_976_ = ((size_t)5ULL);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_sub(v_depth_965_, v___x_978_);
v___x_980_ = lean_usize_mul(v___x_976_, v___x_979_);
v_h_981_ = lean_usize_shift_right(v_h_975_, v___x_980_);
v___x_982_ = lean_nat_add(v_i_968_, v___x_977_);
lean_dec(v_i_968_);
lean_inc(v_v_973_);
lean_inc(v_k_972_);
v___x_983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_entries_969_, v_h_981_, v_depth_965_, v_k_972_, v_v_973_);
v_i_968_ = v___x_982_;
v_entries_969_ = v___x_983_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(lean_object* v_depth_985_, lean_object* v_keys_986_, lean_object* v_vals_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
size_t v_depth_boxed_990_; lean_object* v_res_991_; 
v_depth_boxed_990_ = lean_unbox_usize(v_depth_985_);
lean_dec(v_depth_985_);
v_res_991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_boxed_990_, v_keys_986_, v_vals_987_, v_i_988_, v_entries_989_);
lean_dec_ref(v_vals_987_);
lean_dec_ref(v_keys_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
size_t v_x_12379__boxed_997_; size_t v_x_12380__boxed_998_; lean_object* v_res_999_; 
v_x_12379__boxed_997_ = lean_unbox_usize(v_x_993_);
lean_dec(v_x_993_);
v_x_12380__boxed_998_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_999_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_992_, v_x_12379__boxed_997_, v_x_12380__boxed_998_, v_x_995_, v_x_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
uint64_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = l_Lean_instHashableMVarId_hash(v_x_1001_);
v___x_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1000_, v___x_1004_, v___x_1005_, v_x_1001_, v_x_1002_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(lean_object* v_mvarId_1007_, lean_object* v_val_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_mctx_1012_; lean_object* v_cache_1013_; lean_object* v_zetaDeltaFVarIds_1014_; lean_object* v_postponed_1015_; lean_object* v_diag_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1044_; 
v___x_1011_ = lean_st_ref_take(v___y_1009_);
v_mctx_1012_ = lean_ctor_get(v___x_1011_, 0);
v_cache_1013_ = lean_ctor_get(v___x_1011_, 1);
v_zetaDeltaFVarIds_1014_ = lean_ctor_get(v___x_1011_, 2);
v_postponed_1015_ = lean_ctor_get(v___x_1011_, 3);
v_diag_1016_ = lean_ctor_get(v___x_1011_, 4);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1018_ = v___x_1011_;
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_diag_1016_);
lean_inc(v_postponed_1015_);
lean_inc(v_zetaDeltaFVarIds_1014_);
lean_inc(v_cache_1013_);
lean_inc(v_mctx_1012_);
lean_dec(v___x_1011_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1044_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_depth_1020_; lean_object* v_levelAssignDepth_1021_; lean_object* v_lmvarCounter_1022_; lean_object* v_mvarCounter_1023_; lean_object* v_lDecls_1024_; lean_object* v_decls_1025_; lean_object* v_userNames_1026_; lean_object* v_lAssignment_1027_; lean_object* v_eAssignment_1028_; lean_object* v_dAssignment_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_depth_1020_ = lean_ctor_get(v_mctx_1012_, 0);
v_levelAssignDepth_1021_ = lean_ctor_get(v_mctx_1012_, 1);
v_lmvarCounter_1022_ = lean_ctor_get(v_mctx_1012_, 2);
v_mvarCounter_1023_ = lean_ctor_get(v_mctx_1012_, 3);
v_lDecls_1024_ = lean_ctor_get(v_mctx_1012_, 4);
v_decls_1025_ = lean_ctor_get(v_mctx_1012_, 5);
v_userNames_1026_ = lean_ctor_get(v_mctx_1012_, 6);
v_lAssignment_1027_ = lean_ctor_get(v_mctx_1012_, 7);
v_eAssignment_1028_ = lean_ctor_get(v_mctx_1012_, 8);
v_dAssignment_1029_ = lean_ctor_get(v_mctx_1012_, 9);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_mctx_1012_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v_mctx_1012_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_dAssignment_1029_);
lean_inc(v_eAssignment_1028_);
lean_inc(v_lAssignment_1027_);
lean_inc(v_userNames_1026_);
lean_inc(v_decls_1025_);
lean_inc(v_lDecls_1024_);
lean_inc(v_mvarCounter_1023_);
lean_inc(v_lmvarCounter_1022_);
lean_inc(v_levelAssignDepth_1021_);
lean_inc(v_depth_1020_);
lean_dec(v_mctx_1012_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_eAssignment_1028_, v_mvarId_1007_, v_val_1008_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 8, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_depth_1020_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_levelAssignDepth_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_lmvarCounter_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_mvarCounter_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_lDecls_1024_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_decls_1025_);
lean_ctor_set(v_reuseFailAlloc_1042_, 6, v_userNames_1026_);
lean_ctor_set(v_reuseFailAlloc_1042_, 7, v_lAssignment_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 8, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 9, v_dAssignment_1029_);
v___x_1035_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1035_);
v___x_1037_ = v___x_1018_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_cache_1013_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_zetaDeltaFVarIds_1014_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_postponed_1015_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_diag_1016_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_st_ref_set(v___y_1009_, v___x_1037_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(lean_object* v_mvarId_1045_, lean_object* v_val_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1045_, v_val_1046_, v___y_1047_);
lean_dec(v___y_1047_);
return v_res_1049_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1));
v___x_1054_ = l_Lean_MessageData_ofFormat(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(lean_object* v_upperBound_1057_, lean_object* v___y_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v_a_1061_, lean_object* v_mvarId_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_lt(v_a_1063_, v_upperBound_1057_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_a_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v___x_1059_);
lean_dec_ref(v___y_1058_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_b_1064_);
return v___x_1071_;
}
else
{
lean_object* v_snd_1072_; lean_object* v_fst_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1155_; 
v_snd_1072_ = lean_ctor_get(v_b_1064_, 1);
v_fst_1073_ = lean_ctor_get(v_b_1064_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_b_1064_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1075_ = v_b_1064_;
v_isShared_1076_ = v_isSharedCheck_1155_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1072_);
lean_inc(v_fst_1073_);
lean_dec(v_b_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1155_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1154_; 
v_fst_1077_ = lean_ctor_get(v_snd_1072_, 0);
v_snd_1078_ = lean_ctor_get(v_snd_1072_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_snd_1072_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1080_ = v_snd_1072_;
v_isShared_1081_ = v_isSharedCheck_1154_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v_snd_1072_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1154_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; 
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v_fst_1077_);
v___x_1082_ = lean_whnf(v_fst_1077_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1145_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v_fst_1084_ = lean_ctor_get(v_snd_1078_, 0);
v_snd_1085_ = lean_ctor_get(v_snd_1078_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_snd_1078_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1087_ = v_snd_1078_;
v_isShared_1088_ = v_isSharedCheck_1145_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1084_);
lean_dec(v_snd_1078_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1145_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v_a_1091_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_a_1083_) == 7)
{
lean_object* v_binderType_1094_; lean_object* v_body_1095_; lean_object* v___x_1096_; lean_object* v___y_1098_; uint8_t v___x_1123_; 
lean_dec(v_fst_1077_);
v_binderType_1094_ = lean_ctor_get(v_a_1083_, 1);
lean_inc_ref(v_binderType_1094_);
v_body_1095_ = lean_ctor_get(v_a_1083_, 2);
lean_inc_ref(v_body_1095_);
lean_dec_ref_known(v_a_1083_, 3);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_nat_dec_lt(v___x_1089_, v___x_1060_);
if (v___x_1123_ == 0)
{
lean_inc(v_a_1061_);
v___y_1098_ = v_a_1061_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1124_; 
lean_inc(v_snd_1085_);
lean_inc(v_a_1061_);
v___x_1124_ = l_Lean_Name_num___override(v_a_1061_, v_snd_1085_);
v___y_1098_ = v___x_1124_;
goto v___jp_1097_;
}
v___jp_1097_:
{
uint8_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = 2;
lean_inc_ref(v___x_1059_);
lean_inc_ref(v___y_1058_);
v___x_1100_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_1058_, v___x_1059_, v_binderType_1094_, v___x_1099_, v___y_1098_, v___x_1096_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_n(v_a_1101_, 2);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = l_Lean_Expr_app___override(v_fst_1073_, v_a_1101_);
v___x_1103_ = l_Lean_Expr_mvarId_x21(v_a_1101_);
lean_dec(v_a_1101_);
v___x_1104_ = lean_array_push(v_fst_1084_, v___x_1103_);
v___x_1105_ = lean_nat_add(v_snd_1085_, v___x_1089_);
lean_dec(v_snd_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1105_);
lean_ctor_set(v___x_1087_, 0, v___x_1104_);
v___x_1107_ = v___x_1087_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1107_);
lean_ctor_set(v___x_1080_, 0, v_body_1095_);
v___x_1109_ = v___x_1080_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_body_1095_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1109_);
lean_ctor_set(v___x_1075_, 0, v___x_1102_);
v___x_1111_ = v___x_1075_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_a_1091_ = v___x_1111_;
goto v___jp_1090_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_body_1095_);
lean_del_object(v___x_1087_);
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
lean_del_object(v___x_1080_);
lean_del_object(v___x_1075_);
lean_dec(v_fst_1073_);
lean_dec(v_a_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v___x_1059_);
lean_dec_ref(v___y_1058_);
v_a_1115_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1100_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1100_);
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
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_a_1083_);
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
v___x_1126_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3);
lean_inc(v_mvarId_1062_);
v___x_1127_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1125_, v_mvarId_1062_, v___x_1126_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref_known(v___x_1127_, 1);
if (v_isShared_1088_ == 0)
{
v___x_1129_ = v___x_1087_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_fst_1084_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_snd_1085_);
v___x_1129_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1129_);
v___x_1131_ = v___x_1080_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1131_);
v___x_1133_ = v___x_1075_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_fst_1073_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
v_a_1091_ = v___x_1133_;
goto v___jp_1090_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_1087_);
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
lean_del_object(v___x_1080_);
lean_dec(v_fst_1077_);
lean_del_object(v___x_1075_);
lean_dec(v_fst_1073_);
lean_dec(v_a_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v___x_1059_);
lean_dec_ref(v___y_1058_);
v_a_1137_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1127_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1127_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_nat_add(v_a_1063_, v___x_1089_);
lean_dec(v_a_1063_);
v_a_1063_ = v___x_1092_;
v_b_1064_ = v_a_1091_;
goto _start;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_del_object(v___x_1080_);
lean_dec(v_snd_1078_);
lean_dec(v_fst_1077_);
lean_del_object(v___x_1075_);
lean_dec(v_fst_1073_);
lean_dec(v_a_1063_);
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v___x_1059_);
lean_dec_ref(v___y_1058_);
v_a_1146_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1082_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1082_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(lean_object* v_upperBound_1156_, lean_object* v___y_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v_a_1160_, lean_object* v_mvarId_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1156_, v___y_1157_, v___x_1158_, v___x_1159_, v_a_1160_, v_mvarId_1161_, v_a_1162_, v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___x_1159_);
lean_dec(v_upperBound_1156_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(size_t v_sz_1170_, size_t v_i_1171_, lean_object* v_bs_1172_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_lt(v_i_1171_, v_sz_1170_);
if (v___x_1173_ == 0)
{
return v_bs_1172_;
}
else
{
lean_object* v_v_1174_; lean_object* v___x_1175_; lean_object* v_bs_x27_1176_; lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_v_1174_ = lean_array_uget(v_bs_1172_, v_i_1171_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v_bs_x27_1176_ = lean_array_uset(v_bs_1172_, v_i_1171_, v___x_1175_);
v___x_1177_ = l_Lean_mkFVar(v_v_1174_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1171_, v___x_1178_);
v___x_1180_ = lean_array_uset(v_bs_x27_1176_, v_i_1171_, v___x_1177_);
v_i_1171_ = v___x_1179_;
v_bs_1172_ = v___x_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(lean_object* v_sz_1182_, lean_object* v_i_1183_, lean_object* v_bs_1184_){
_start:
{
size_t v_sz_boxed_1185_; size_t v_i_boxed_1186_; lean_object* v_res_1187_; 
v_sz_boxed_1185_ = lean_unbox_usize(v_sz_1182_);
lean_dec(v_sz_1182_);
v_i_boxed_1186_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_boxed_1185_, v_i_boxed_1186_, v_bs_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0(lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_mvarId_1195_, lean_object* v_fvarId_1196_, lean_object* v_indices_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_sz_1203_ = lean_array_size(v_indices_1197_);
v___x_1204_ = ((size_t)0ULL);
lean_inc_ref(v_indices_1197_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_1203_, v___x_1204_, v_indices_1197_);
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2));
lean_inc_ref(v_a_1193_);
lean_inc(v_fvarId_1196_);
lean_inc(v_mvarId_1195_);
v___x_1207_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_1195_, v___x_1206_, v_fvarId_1196_, v_a_1193_, v___x_1205_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v_lctx_1209_; lean_object* v_localInstances_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___y_1215_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v_lctx_1209_ = lean_ctor_get(v___y_1198_, 2);
v_localInstances_1210_ = lean_ctor_get(v___y_1198_, 3);
v___x_1211_ = 1;
lean_inc(v_fvarId_1196_);
lean_inc_ref(v_lctx_1209_);
v___x_1212_ = l_Lean_LocalContext_setKind(v_lctx_1209_, v_fvarId_1196_, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v_indices_1197_);
v___x_1258_ = lean_nat_dec_lt(v___x_1213_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_dec_ref(v_indices_1197_);
v___y_1215_ = v___x_1212_;
goto v___jp_1214_;
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_nat_dec_le(v___x_1257_, v___x_1257_);
if (v___x_1259_ == 0)
{
if (v___x_1258_ == 0)
{
lean_dec_ref(v_indices_1197_);
v___y_1215_ = v___x_1212_;
goto v___jp_1214_;
}
else
{
size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_usize_of_nat(v___x_1257_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1197_, v___x_1204_, v___x_1260_, v___x_1212_);
lean_dec_ref(v_indices_1197_);
v___y_1215_ = v___x_1261_;
goto v___jp_1214_;
}
}
else
{
size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_usize_of_nat(v___x_1257_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_1197_, v___x_1204_, v___x_1262_, v___x_1212_);
lean_dec_ref(v_indices_1197_);
v___y_1215_ = v___x_1263_;
goto v___jp_1214_;
}
}
v___jp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_mkAppN(v_a_1208_, v___x_1205_);
lean_dec_ref(v___x_1205_);
v___x_1217_ = l_Lean_mkFVar(v_fvarId_1196_);
v___x_1218_ = l_Lean_Expr_app___override(v___x_1216_, v___x_1217_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc_ref(v___x_1218_);
v___x_1219_ = lean_infer_type(v___x_1218_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = l_Lean_Meta_RecursorInfo_numMinors(v_a_1193_);
lean_dec_ref(v_a_1193_);
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__1));
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1220_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1218_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
lean_inc(v_mvarId_1195_);
lean_inc_ref(v_localInstances_1210_);
v___x_1225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v___x_1221_, v___y_1215_, v_localInstances_1210_, v___x_1221_, v_a_1194_, v_mvarId_1195_, v___x_1213_, v___x_1224_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___x_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1239_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v_fst_1227_ = lean_ctor_get(v_a_1226_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v_a_1226_, 1);
lean_inc(v_snd_1228_);
lean_dec(v_a_1226_);
v___x_1229_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1195_, v_fst_1227_, v___y_1199_);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1240_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_snd_1233_; lean_object* v_fst_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v_snd_1233_ = lean_ctor_get(v_snd_1228_, 1);
lean_inc(v_snd_1233_);
lean_dec(v_snd_1228_);
v_fst_1234_ = lean_ctor_get(v_snd_1233_, 0);
lean_inc(v_fst_1234_);
lean_dec(v_snd_1233_);
v___x_1235_ = lean_array_to_list(v_fst_1234_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
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
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_mvarId_1195_);
v_a_1241_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1225_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1225_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
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
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___y_1215_);
lean_dec(v_mvarId_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
v_a_1249_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1219_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1219_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_indices_1197_);
lean_dec(v_fvarId_1196_);
lean_dec(v_mvarId_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
v_a_1264_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1207_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1207_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__0___boxed(lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_mvarId_1274_, lean_object* v_fvarId_1275_, lean_object* v_indices_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1272_, v_a_1273_, v_mvarId_1274_, v_fvarId_1275_, v_indices_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = l_Lean_Name_isAnonymous(v_declHint_1305_);
if (v___x_1310_ == 0)
{
uint8_t v_isExporting_1311_; 
v_isExporting_1311_ = lean_ctor_get_uint8(v_env_1309_, sizeof(void*)*8);
if (v_isExporting_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_msg_1304_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
lean_inc_ref(v_env_1309_);
v___x_1313_ = l_Lean_Environment_setExporting(v_env_1309_, v___x_1310_);
lean_inc(v_declHint_1305_);
lean_inc_ref(v___x_1313_);
v___x_1314_ = l_Lean_Environment_contains(v___x_1313_, v_declHint_1305_, v_isExporting_1311_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v___x_1313_);
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_msg_1304_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_c_1321_; lean_object* v___x_1322_; 
v___x_1316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
v___x_1317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
v___x_1318_ = l_Lean_Options_empty;
v___x_1319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1313_);
lean_ctor_set(v___x_1319_, 1, v___x_1316_);
lean_ctor_set(v___x_1319_, 2, v___x_1317_);
lean_ctor_set(v___x_1319_, 3, v___x_1318_);
lean_inc(v_declHint_1305_);
v___x_1320_ = l_Lean_MessageData_ofConstName(v_declHint_1305_, v___x_1310_);
v_c_1321_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1321_, 0, v___x_1319_);
lean_ctor_set(v_c_1321_, 1, v___x_1320_);
v___x_1322_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1309_, v_declHint_1305_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1323_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_c_1321_);
v___x_1325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = l_Lean_MessageData_note(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_msg_1304_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
else
{
lean_object* v_val_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1365_; 
v_val_1330_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1332_ = v___x_1322_;
v_isShared_1333_ = v_isSharedCheck_1365_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_val_1330_);
lean_dec(v___x_1322_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1365_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_mod_1337_; uint8_t v___x_1338_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Lean_Environment_header(v_env_1309_);
lean_dec_ref(v_env_1309_);
v___x_1336_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1335_);
v_mod_1337_ = lean_array_get(v___x_1334_, v___x_1336_, v_val_1330_);
lean_dec(v_val_1330_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = l_Lean_isPrivateName(v_declHint_1305_);
lean_dec(v_declHint_1305_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1339_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_c_1321_);
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_MessageData_ofName(v_mod_1337_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_MessageData_note(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_msg_1304_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1348_);
v___x_1350_ = v___x_1332_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1352_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_c_1321_);
v___x_1354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_MessageData_ofName(v_mod_1337_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_MessageData_note(v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_msg_1304_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1361_);
v___x_1363_ = v___x_1332_;
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
}
}
}
}
}
else
{
lean_object* v___x_1366_; 
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_msg_1304_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1367_, lean_object* v_declHint_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1367_, v_declHint_1368_, v___y_1369_);
lean_dec(v___y_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(lean_object* v_msg_1372_, lean_object* v_declHint_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
v___x_1379_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1372_, v_declHint_1373_, v___y_1377_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = l_Lean_unknownIdentifierMessageTag;
v___x_1385_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(lean_object* v_msg_1390_, lean_object* v_declHint_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1390_, v_declHint_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(lean_object* v_msgData_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; lean_object* v_mctx_1407_; lean_object* v_lctx_1408_; lean_object* v_options_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = lean_st_ref_get(v___y_1400_);
v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_mctx_1407_);
lean_dec(v___x_1406_);
v_lctx_1408_ = lean_ctor_get(v___y_1399_, 2);
v_options_1409_ = lean_ctor_get(v___y_1401_, 2);
lean_inc_ref(v_options_1409_);
lean_inc_ref(v_lctx_1408_);
v___x_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1410_, 0, v_env_1405_);
lean_ctor_set(v___x_1410_, 1, v_mctx_1407_);
lean_ctor_set(v___x_1410_, 2, v_lctx_1408_);
lean_ctor_set(v___x_1410_, 3, v_options_1409_);
v___x_1411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v_msgData_1398_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(lean_object* v_msgData_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(lean_object* v_msg_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_ref_1426_; lean_object* v___x_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_ref_1426_ = lean_ctor_get(v___y_1423_, 5);
v___x_1427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msg_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_inc(v_ref_1426_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_ref_1426_);
lean_ctor_set(v___x_1432_, 1, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object* v_ref_1444_, lean_object* v_msg_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_fileName_1451_; lean_object* v_fileMap_1452_; lean_object* v_options_1453_; lean_object* v_currRecDepth_1454_; lean_object* v_maxRecDepth_1455_; lean_object* v_ref_1456_; lean_object* v_currNamespace_1457_; lean_object* v_openDecls_1458_; lean_object* v_initHeartbeats_1459_; lean_object* v_maxHeartbeats_1460_; lean_object* v_quotContext_1461_; lean_object* v_currMacroScope_1462_; uint8_t v_diag_1463_; lean_object* v_cancelTk_x3f_1464_; uint8_t v_suppressElabErrors_1465_; lean_object* v_inheritedTraceOptions_1466_; lean_object* v_ref_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_fileName_1451_ = lean_ctor_get(v___y_1448_, 0);
v_fileMap_1452_ = lean_ctor_get(v___y_1448_, 1);
v_options_1453_ = lean_ctor_get(v___y_1448_, 2);
v_currRecDepth_1454_ = lean_ctor_get(v___y_1448_, 3);
v_maxRecDepth_1455_ = lean_ctor_get(v___y_1448_, 4);
v_ref_1456_ = lean_ctor_get(v___y_1448_, 5);
v_currNamespace_1457_ = lean_ctor_get(v___y_1448_, 6);
v_openDecls_1458_ = lean_ctor_get(v___y_1448_, 7);
v_initHeartbeats_1459_ = lean_ctor_get(v___y_1448_, 8);
v_maxHeartbeats_1460_ = lean_ctor_get(v___y_1448_, 9);
v_quotContext_1461_ = lean_ctor_get(v___y_1448_, 10);
v_currMacroScope_1462_ = lean_ctor_get(v___y_1448_, 11);
v_diag_1463_ = lean_ctor_get_uint8(v___y_1448_, sizeof(void*)*14);
v_cancelTk_x3f_1464_ = lean_ctor_get(v___y_1448_, 12);
v_suppressElabErrors_1465_ = lean_ctor_get_uint8(v___y_1448_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1466_ = lean_ctor_get(v___y_1448_, 13);
v_ref_1467_ = l_Lean_replaceRef(v_ref_1444_, v_ref_1456_);
lean_inc_ref(v_inheritedTraceOptions_1466_);
lean_inc(v_cancelTk_x3f_1464_);
lean_inc(v_currMacroScope_1462_);
lean_inc(v_quotContext_1461_);
lean_inc(v_maxHeartbeats_1460_);
lean_inc(v_initHeartbeats_1459_);
lean_inc(v_openDecls_1458_);
lean_inc(v_currNamespace_1457_);
lean_inc(v_maxRecDepth_1455_);
lean_inc(v_currRecDepth_1454_);
lean_inc_ref(v_options_1453_);
lean_inc_ref(v_fileMap_1452_);
lean_inc_ref(v_fileName_1451_);
v___x_1468_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1468_, 0, v_fileName_1451_);
lean_ctor_set(v___x_1468_, 1, v_fileMap_1452_);
lean_ctor_set(v___x_1468_, 2, v_options_1453_);
lean_ctor_set(v___x_1468_, 3, v_currRecDepth_1454_);
lean_ctor_set(v___x_1468_, 4, v_maxRecDepth_1455_);
lean_ctor_set(v___x_1468_, 5, v_ref_1467_);
lean_ctor_set(v___x_1468_, 6, v_currNamespace_1457_);
lean_ctor_set(v___x_1468_, 7, v_openDecls_1458_);
lean_ctor_set(v___x_1468_, 8, v_initHeartbeats_1459_);
lean_ctor_set(v___x_1468_, 9, v_maxHeartbeats_1460_);
lean_ctor_set(v___x_1468_, 10, v_quotContext_1461_);
lean_ctor_set(v___x_1468_, 11, v_currMacroScope_1462_);
lean_ctor_set(v___x_1468_, 12, v_cancelTk_x3f_1464_);
lean_ctor_set(v___x_1468_, 13, v_inheritedTraceOptions_1466_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*14, v_diag_1463_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*14 + 1, v_suppressElabErrors_1465_);
v___x_1469_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1445_, v___y_1446_, v___y_1447_, v___x_1468_, v___y_1449_);
lean_dec_ref_known(v___x_1468_, 14);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1470_, v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v_ref_1470_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_ref_1478_, lean_object* v_msg_1479_, lean_object* v_declHint_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v___x_1488_; 
v___x_1486_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_1479_, v_declHint_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1478_, v_a_1487_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1489_, lean_object* v_msg_1490_, lean_object* v_declHint_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1489_, v_msg_1490_, v_declHint_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v_ref_1489_);
return v_res_1497_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1501_, lean_object* v_constName_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1508_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1509_ = 0;
lean_inc(v_constName_1502_);
v___x_1510_ = l_Lean_MessageData_ofConstName(v_constName_1502_, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1508_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_obj_once(&l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1, &l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once, _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1501_, v___x_1513_, v_constName_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1515_, lean_object* v_constName_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1515_, v_constName_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v_ref_1515_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(lean_object* v_constName_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_ref_1529_; lean_object* v___x_1530_; 
v_ref_1529_ = lean_ctor_get(v___y_1526_, 5);
v___x_1530_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1529_, v_constName_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(lean_object* v_constName_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v_env_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = lean_st_ref_get(v___y_1542_);
v_env_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_env_1545_);
lean_dec(v___x_1544_);
v___x_1546_ = 0;
lean_inc(v_constName_1538_);
v___x_1547_ = l_Lean_Environment_find_x3f(v_env_1545_, v_constName_1538_, v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_constName_1538_);
v_val_1549_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(lean_object* v_constName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_constName_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1(lean_object* v_mvarId_1570_, lean_object* v_e_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
lean_inc(v_mvarId_1570_);
v___x_1577_ = l_Lean_MVarId_getTag(v_mvarId_1570_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
lean_inc_ref(v_e_1571_);
v___x_1579_ = lean_infer_type(v_e_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
v___x_1581_ = lean_whnf(v_a_1580_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Expr_getAppFn(v_a_1582_);
if (lean_obj_tag(v___x_1583_) == 4)
{
lean_object* v_declName_1584_; lean_object* v___x_1585_; 
v_declName_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_n(v_declName_1584_, 2);
lean_dec_ref_known(v___x_1583_, 2);
v___x_1585_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(v_declName_1584_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
if (lean_obj_tag(v_a_1586_) == 5)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref_known(v_a_1586_, 1);
v___x_1587_ = l_Lean_mkCasesOnName(v_declName_1584_);
v___x_1588_ = lean_box(0);
v___x_1589_ = l_Lean_Meta_mkRecursorInfo(v___x_1587_, v___x_1588_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = l_Lean_Meta_RecursorInfo_numIndices(v_a_1590_);
v___x_1593_ = lean_nat_dec_lt(v___x_1591_, v___x_1592_);
lean_dec(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_inc_ref(v_e_1571_);
v___x_1594_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v_mvarId_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; uint8_t v___x_1618_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1618_ = lean_unbox(v_a_1595_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_inc_ref(v_e_1571_);
v___x_1619_ = l_Lean_Meta_isProof(v_e_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1623_ = l_Lean_Core_mkFreshUserName(v___x_1622_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__3));
v___x_1626_ = l_Lean_MVarId_assertExt(v_mvarId_1570_, v_a_1624_, v_a_1582_, v_e_1571_, v___x_1625_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_mvarId_1597_ = v_a_1627_;
v___y_1598_ = v___y_1572_;
v___y_1599_ = v___y_1573_;
v___y_1600_ = v___y_1574_;
v___y_1601_ = v___y_1575_;
goto v___jp_1596_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
v_a_1628_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1626_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1590_);
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1636_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1623_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1623_);
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
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__1___closed__1));
v___x_1645_ = l_Lean_Core_mkFreshUserName(v___x_1644_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_MVarId_assert(v_mvarId_1570_, v_a_1646_, v_a_1582_, v_e_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v_mvarId_1597_ = v_a_1648_;
v___y_1598_ = v___y_1572_;
v___y_1599_ = v___y_1573_;
v___y_1600_ = v___y_1574_;
v___y_1601_ = v___y_1575_;
goto v___jp_1596_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
v_a_1649_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1647_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1647_);
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
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1590_);
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1657_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1645_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1645_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1590_);
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1665_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1619_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1619_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1582_);
v___x_1673_ = l_Lean_Expr_fvarId_x21(v_e_1571_);
lean_dec_ref(v_e_1571_);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1675_ = l_Lean_Meta_Grind_cases___lam__0(v_a_1590_, v_a_1578_, v_mvarId_1570_, v___x_1673_, v___x_1674_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v___x_1675_;
}
v___jp_1596_:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_unbox(v_a_1595_);
lean_dec(v_a_1595_);
v___x_1603_ = l_Lean_Meta_intro1Core(v_mvarId_1597_, v___x_1602_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v_fst_1605_; lean_object* v_snd_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v_fst_1605_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_fst_1605_);
v_snd_1606_ = lean_ctor_get(v_a_1604_, 1);
lean_inc_n(v_snd_1606_, 2);
lean_dec(v_a_1604_);
v___x_1607_ = ((lean_object*)(l_Lean_Meta_Grind_cases___lam__0___closed__0));
v___x_1608_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1608_, 0, v_a_1590_);
lean_closure_set(v___x_1608_, 1, v_a_1578_);
lean_closure_set(v___x_1608_, 2, v_snd_1606_);
lean_closure_set(v___x_1608_, 3, v_fst_1605_);
lean_closure_set(v___x_1608_, 4, v___x_1607_);
v___x_1609_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_snd_1606_, v___x_1608_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v___x_1609_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
v_a_1610_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1603_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1603_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1676_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1594_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1594_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_a_1582_);
v___x_1684_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1570_, v_e_1571_, v___x_1588_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v_mvarId_1686_; lean_object* v_indicesFVarIds_1687_; lean_object* v_fvarId_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v_mvarId_1686_ = lean_ctor_get(v_a_1685_, 0);
lean_inc_n(v_mvarId_1686_, 2);
v_indicesFVarIds_1687_ = lean_ctor_get(v_a_1685_, 1);
lean_inc_ref(v_indicesFVarIds_1687_);
v_fvarId_1688_ = lean_ctor_get(v_a_1685_, 2);
lean_inc(v_fvarId_1688_);
lean_dec(v_a_1685_);
v___x_1689_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__0___boxed), 10, 5);
lean_closure_set(v___x_1689_, 0, v_a_1590_);
lean_closure_set(v___x_1689_, 1, v_a_1578_);
lean_closure_set(v___x_1689_, 2, v_mvarId_1686_);
lean_closure_set(v___x_1689_, 3, v_fvarId_1688_);
lean_closure_set(v___x_1689_, 4, v_indicesFVarIds_1687_);
v___x_1690_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1686_, v___x_1689_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v___x_1690_;
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
v_a_1691_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1684_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1684_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1699_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1589_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1589_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec(v_a_1586_);
lean_dec(v_declName_1584_);
lean_dec(v_a_1578_);
v___x_1707_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1570_, v_e_1571_, v_a_1582_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v___x_1707_;
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_declName_1584_);
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1708_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1585_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1585_);
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
else
{
lean_object* v___x_1716_; 
lean_dec_ref(v___x_1583_);
lean_dec(v_a_1578_);
v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_1570_, v_e_1571_, v_a_1582_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v___x_1716_;
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1717_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1581_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1581_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1578_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1725_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1579_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1579_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_e_1571_);
lean_dec(v_mvarId_1570_);
v_a_1733_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1577_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1577_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___lam__1___boxed(lean_object* v_mvarId_1741_, lean_object* v_e_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Meta_Grind_cases___lam__1(v_mvarId_1741_, v_e_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases(lean_object* v_mvarId_1749_, lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___f_1756_; lean_object* v___x_1757_; 
lean_inc(v_mvarId_1749_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_cases___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1756_, 0, v_mvarId_1749_);
lean_closure_set(v___f_1756_, 1, v_e_1750_);
v___x_1757_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_1749_, v___f_1756_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_cases___boxed(lean_object* v_mvarId_1758_, lean_object* v_e_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_Grind_cases(v_mvarId_1758_, v_e_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(lean_object* v_mvarId_1766_, lean_object* v_val_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(v_mvarId_1766_, v_val_1767_, v___y_1769_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(lean_object* v_mvarId_1774_, lean_object* v_val_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(v_mvarId_1774_, v_val_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(lean_object* v_upperBound_1782_, lean_object* v___y_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_a_1786_, lean_object* v_mvarId_1787_, lean_object* v_inst_1788_, lean_object* v_R_1789_, lean_object* v_a_1790_, lean_object* v_b_1791_, lean_object* v_c_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v_upperBound_1782_, v___y_1783_, v___x_1784_, v___x_1785_, v_a_1786_, v_mvarId_1787_, v_a_1790_, v_b_1791_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(lean_object* v_upperBound_1799_, lean_object* v___y_1800_, lean_object* v___x_1801_, lean_object* v___x_1802_, lean_object* v_a_1803_, lean_object* v_mvarId_1804_, lean_object* v_inst_1805_, lean_object* v_R_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_c_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(v_upperBound_1799_, v___y_1800_, v___x_1801_, v___x_1802_, v_a_1803_, v_mvarId_1804_, v_inst_1805_, v_R_1806_, v_a_1807_, v_b_1808_, v_c_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___x_1802_);
lean_dec(v_upperBound_1799_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(lean_object* v_00_u03b1_1816_, lean_object* v_constName_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_constName_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(v_00_u03b1_1824_, v_constName_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(lean_object* v_00_u03b2_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_x_1833_, v_x_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1837_, lean_object* v_ref_1838_, lean_object* v_constName_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_1838_, v_constName_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_ref_1847_, lean_object* v_constName_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(v_00_u03b1_1846_, v_ref_1847_, v_constName_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v_ref_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1855_, lean_object* v_x_1856_, size_t v_x_1857_, size_t v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_1856_, v_x_1857_, v_x_1858_, v_x_1859_, v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
size_t v_x_13902__boxed_1868_; size_t v_x_13903__boxed_1869_; lean_object* v_res_1870_; 
v_x_13902__boxed_1868_ = lean_unbox_usize(v_x_1864_);
lean_dec(v_x_1864_);
v_x_13903__boxed_1869_ = lean_unbox_usize(v_x_1865_);
lean_dec(v_x_1865_);
v_res_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(v_00_u03b2_1862_, v_x_1863_, v_x_13902__boxed_1868_, v_x_13903__boxed_1869_, v_x_1866_, v_x_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_1871_, lean_object* v_ref_1872_, lean_object* v_msg_1873_, lean_object* v_declHint_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_1872_, v_msg_1873_, v_declHint_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_ref_1882_, lean_object* v_msg_1883_, lean_object* v_declHint_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_1881_, v_ref_1882_, v_msg_1883_, v_declHint_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v_ref_1882_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1891_, lean_object* v_n_1892_, lean_object* v_k_1893_, lean_object* v_v_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v_n_1892_, v_k_1893_, v_v_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(lean_object* v_00_u03b2_1896_, size_t v_depth_1897_, lean_object* v_keys_1898_, lean_object* v_vals_1899_, lean_object* v_heq_1900_, lean_object* v_i_1901_, lean_object* v_entries_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_1897_, v_keys_1898_, v_vals_1899_, v_i_1901_, v_entries_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1904_, lean_object* v_depth_1905_, lean_object* v_keys_1906_, lean_object* v_vals_1907_, lean_object* v_heq_1908_, lean_object* v_i_1909_, lean_object* v_entries_1910_){
_start:
{
size_t v_depth_boxed_1911_; lean_object* v_res_1912_; 
v_depth_boxed_1911_ = lean_unbox_usize(v_depth_1905_);
lean_dec(v_depth_1905_);
v_res_1912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(v_00_u03b2_1904_, v_depth_boxed_1911_, v_keys_1906_, v_vals_1907_, v_heq_1908_, v_i_1909_, v_entries_1910_);
lean_dec_ref(v_vals_1907_);
lean_dec_ref(v_keys_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(lean_object* v_msg_1913_, lean_object* v_declHint_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_1913_, v_declHint_1914_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_1921_, lean_object* v_declHint_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_1921_, v_declHint_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object* v_00_u03b1_1929_, lean_object* v_ref_1930_, lean_object* v_msg_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_1930_, v_msg_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1938_, lean_object* v_ref_1939_, lean_object* v_msg_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_1938_, v_ref_1939_, v_msg_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v_ref_1939_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_x_1948_, v_x_1949_, v_x_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_1953_, lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_1961_, v_msg_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1968_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

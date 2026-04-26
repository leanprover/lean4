// Lean compiler output
// Module: Lean.Linter.EnvLinter.Basic
// Imports: public import Lean.Structure public import Lean.Elab.InfoTree.Main import Lean.ExtraModUses public import Lean.Linter.EnvLinter.Nolint
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
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_belowSuffix;
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_recOnSuffix;
extern lean_object* l_Lean_casesOnSuffix;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_functor"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorElim"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ctorElimType"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__11_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__13_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__10_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__14_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__9_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__15_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__8_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__16_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__17_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__6_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__18_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__5_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__19_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__4_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__20_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "brecOn_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__33_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__34_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__32_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__35_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__31_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__36_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__30_value),((lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__37_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38_value;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unsafe_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44;
static const lean_string_object l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45 = (const lean_object*)&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 32, 157, 0, 199, 45, 83, 147)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "envLinterExt"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 34, 157, 198, 119, 92, 66, 12)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "builtin_env_linter"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 180, 153, 91, 141, 98, 2, 80)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " clippy"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` must have type `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, got `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " but is only marked `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid attribute `builtin_env_linter`, declaration `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` must be marked as `public` and `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " but is only marked `public`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid attribute `builtin_env_linter`, linter `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `builtin_env_linter`, must be global"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 77, 64, 120, 151, 50, 41, 244)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 75, 158, 206, 205, 238, 69, 21)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 12, 34, 233, 215, 60, 102, 16)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 128, 199, 109, 85, 222, 11)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(202, 197, 79, 202, 254, 40, 158, 224)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 170, 47, 185, 53, 142, 137, 13)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 191, 200, 41, 134, 97, 182, 145)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 137, 166, 37, 185, 248, 93, 214)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 129, 252, 190, 49, 60, 207)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 162, 40, 223, 118, 24, 158, 134)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 50, 203, 113, 71, 15, 125, 124)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 43, 132, 57, 147, 43, 102, 84)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 8, 91, 236, 76, 189, 200, 47)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Use this declaration as a linting test in `lake builtin-lint`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___f_5_; 
v___x_4_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_5_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5_, 0, v___x_4_);
return v___f_5_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__21));
v___x_43_ = l_Lean_belowSuffix;
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__22);
v___x_46_ = l_Lean_brecOnSuffix;
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__23);
v___x_49_ = l_Lean_recOnSuffix;
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__24);
v___x_52_ = l_Lean_casesOnSuffix;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26));
v___x_56_ = lean_string_utf8_byte_size(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28));
v___x_59_ = lean_string_utf8_byte_size(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39));
v___x_81_ = lean_string_utf8_byte_size(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41));
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43));
v___x_87_ = lean_string_utf8_byte_size(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45));
v___x_90_ = lean_string_utf8_byte_size(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg(lean_object* v_decl_91_, lean_object* v_a_92_){
_start:
{
uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = l_Lean_Name_hasMacroScopes(v_decl_91_);
v___x_95_ = 1;
if (v___x_94_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = l_Lean_Name_isInternal(v_decl_91_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v_env_98_; uint8_t v___x_99_; 
v___x_97_ = lean_st_ref_get(v_a_92_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref_n(v_env_98_, 2);
lean_dec(v___x_97_);
lean_inc(v_decl_91_);
v___x_99_ = lean_is_reserved_name(v_env_98_, v_decl_91_);
if (v___x_99_ == 0)
{
if (lean_obj_tag(v_decl_91_) == 1)
{
lean_object* v_pre_100_; lean_object* v_str_101_; uint8_t v___y_103_; lean_object* v___x_151_; lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_246_; 
v_pre_100_ = lean_ctor_get(v_decl_91_, 0);
lean_inc_n(v_pre_100_, 2);
v_str_101_ = lean_ctor_get(v_decl_91_, 1);
lean_inc_ref(v_str_101_);
lean_dec_ref(v_decl_91_);
v___x_151_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v_pre_100_, v_a_92_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_246_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_246_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_246_;
goto v_resetjp_153_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__0));
v___x_105_ = l_Lean_Name_str___override(v_pre_100_, v___x_104_);
lean_inc(v___x_105_);
lean_inc_ref(v_env_98_);
v___x_106_ = l_Lean_Environment_find_x3f(v_env_98_, v___x_105_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_148_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_148_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_148_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_148_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
if (lean_obj_tag(v_val_107_) == 5)
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_142_; 
lean_del_object(v___x_109_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_val_107_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_val_107_, 0);
lean_dec(v_unused_143_);
v___x_112_ = v_val_107_;
v_isShared_113_ = v_isSharedCheck_142_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_val_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_142_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__1));
v___x_115_ = lean_string_dec_eq(v_str_101_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_casesOnSuffix;
v___x_117_ = lean_string_dec_eq(v_str_101_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__2));
v___x_119_ = lean_string_dec_eq(v_str_101_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Name_str___override(v___x_105_, v_str_101_);
v___x_121_ = l_Lean_Environment_isConstructor(v_env_98_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_box(v___x_99_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_122_);
v___x_124_ = v___x_112_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_126_);
v___x_128_ = v___x_112_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_130_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_130_);
v___x_132_ = v___x_112_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_134_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_134_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_138_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_138_);
v___x_140_ = v___x_112_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_val_107_);
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_144_ = lean_box(v___x_99_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_144_);
v___x_146_ = v___x_109_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v___x_106_);
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_149_ = lean_box(v___x_99_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
v_resetjp_153_:
{
uint8_t v___y_157_; uint8_t v___y_173_; uint8_t v___y_183_; uint8_t v___x_235_; 
v___x_235_ = lean_unbox(v_a_152_);
lean_dec(v_a_152_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_236_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__45));
v___x_237_ = lean_string_utf8_byte_size(v_str_101_);
v___x_238_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__46);
v___x_239_ = lean_nat_dec_le(v___x_238_, v___x_237_);
if (v___x_239_ == 0)
{
goto v___jp_226_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_string_memcmp(v_str_101_, v___x_236_, v___x_240_, v___x_240_, v___x_238_);
if (v___x_241_ == 0)
{
goto v___jp_226_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_242_ = lean_box(v___x_95_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_244_ = lean_box(v___x_95_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
v___jp_156_:
{
lean_object* v___f_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___f_158_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3);
v___x_159_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__25);
lean_inc_ref(v_str_101_);
v___x_160_ = l_List_elem___redArg(v___f_158_, v_str_101_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
lean_inc_ref(v_str_101_);
v___x_162_ = l_Lean_Name_str___override(v___x_161_, v_str_101_);
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_163_ = l_Lean_isSubobjectField_x3f(v_env_98_, v_pre_100_, v___x_162_);
if (lean_obj_tag(v___x_163_) == 1)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref(v___x_163_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_164_ = lean_box(v___x_95_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_164_);
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_dec(v___x_163_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_157_;
goto v___jp_102_;
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_168_ = lean_box(v___x_95_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_168_);
v___x_170_ = v___x_154_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_174_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__26));
v___x_175_ = lean_string_utf8_byte_size(v_str_101_);
v___x_176_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__27);
v___x_177_ = lean_nat_dec_le(v___x_176_, v___x_175_);
if (v___x_177_ == 0)
{
v___y_157_ = v___y_173_;
goto v___jp_156_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_string_memcmp(v_str_101_, v___x_174_, v___x_178_, v___x_178_, v___x_176_);
if (v___x_179_ == 0)
{
v___y_157_ = v___y_173_;
goto v___jp_156_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_180_ = lean_box(v___x_95_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
v___jp_182_:
{
if (v___y_183_ == 0)
{
lean_object* v___x_184_; 
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_184_ = l_Lean_Environment_find_x3f(v_env_98_, v_pre_100_, v___y_183_);
if (lean_obj_tag(v___x_184_) == 1)
{
lean_object* v_val_185_; 
v_val_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref(v___x_184_);
if (lean_obj_tag(v_val_185_) == 5)
{
lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_199_; 
v_isSharedCheck_199_ = !lean_is_exclusive(v_val_185_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_val_185_, 0);
lean_dec(v_unused_200_);
v___x_187_ = v_val_185_;
v_isShared_188_ = v_isSharedCheck_199_;
goto v_resetjp_186_;
}
else
{
lean_dec(v_val_185_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_199_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__28));
v___x_190_ = lean_string_utf8_byte_size(v_str_101_);
v___x_191_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__29);
v___x_192_ = lean_nat_dec_le(v___x_191_, v___x_190_);
if (v___x_192_ == 0)
{
lean_del_object(v___x_187_);
v___y_173_ = v___y_183_;
goto v___jp_172_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_string_memcmp(v_str_101_, v___x_189_, v___x_193_, v___x_193_, v___x_191_);
if (v___x_194_ == 0)
{
lean_del_object(v___x_187_);
v___y_173_ = v___y_183_;
goto v___jp_172_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_195_ = lean_box(v___x_95_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
lean_ctor_set(v___x_187_, 0, v___x_195_);
v___x_197_ = v___x_187_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_dec(v_val_185_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_183_;
goto v___jp_102_;
}
}
else
{
lean_dec(v___x_184_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_183_;
goto v___jp_102_;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_201_ = lean_box(v___x_95_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
v___jp_203_:
{
uint8_t v___x_204_; 
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_204_ = l_Lean_Environment_isConstructor(v_env_98_, v_pre_100_);
if (v___x_204_ == 0)
{
v___y_183_ = v___x_204_;
goto v___jp_182_;
}
else
{
lean_object* v___f_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___f_205_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__3);
v___x_206_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__38));
lean_inc_ref(v_str_101_);
v___x_207_ = l_List_elem___redArg(v___f_205_, v_str_101_, v___x_206_);
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
}
v___jp_208_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__39));
v___x_210_ = lean_string_utf8_byte_size(v_str_101_);
v___x_211_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__40);
v___x_212_ = lean_nat_dec_le(v___x_211_, v___x_210_);
if (v___x_212_ == 0)
{
goto v___jp_203_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_string_memcmp(v_str_101_, v___x_209_, v___x_213_, v___x_213_, v___x_211_);
if (v___x_214_ == 0)
{
goto v___jp_203_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_215_ = lean_box(v___x_95_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__41));
v___x_219_ = lean_string_utf8_byte_size(v_str_101_);
v___x_220_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__42);
v___x_221_ = lean_nat_dec_le(v___x_220_, v___x_219_);
if (v___x_221_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_memcmp(v_str_101_, v___x_218_, v___x_222_, v___x_222_, v___x_220_);
if (v___x_223_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_224_ = lean_box(v___x_95_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
}
v___jp_226_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_227_ = ((lean_object*)(l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__43));
v___x_228_ = lean_string_utf8_byte_size(v_str_101_);
v___x_229_ = lean_obj_once(&l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44, &l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44_once, _init_l_Lean_Linter_EnvLinter_isAutoDecl___redArg___closed__44);
v___x_230_ = lean_nat_dec_le(v___x_229_, v___x_228_);
if (v___x_230_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_string_memcmp(v_str_101_, v___x_227_, v___x_231_, v___x_231_, v___x_229_);
if (v___x_232_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_233_ = lean_box(v___x_95_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_env_98_);
lean_dec(v_decl_91_);
v___x_247_ = lean_box(v___x_99_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_env_98_);
lean_dec(v_decl_91_);
v___x_249_ = lean_box(v___x_95_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_decl_91_);
v___x_251_ = lean_box(v___x_95_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_decl_91_);
v___x_253_ = lean_box(v___x_95_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg___boxed(lean_object* v_decl_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v_decl_255_, v_a_256_);
lean_dec(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl(lean_object* v_decl_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v_decl_259_, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___boxed(lean_object* v_decl_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Linter_EnvLinter_isAutoDecl(v_decl_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_268_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_box(0);
v___x_270_ = l_Lean_Elab_abortCommandExceptionId;
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
return v_res_276_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_277_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
lean_ctor_set(v___x_282_, 4, v___x_280_);
lean_ctor_set(v___x_282_, 5, v___x_280_);
lean_ctor_set(v___x_282_, 6, v___x_280_);
lean_ctor_set(v___x_282_, 7, v___x_280_);
lean_ctor_set(v___x_282_, 8, v___x_280_);
lean_ctor_set(v___x_282_, 9, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(32u);
v___x_284_ = lean_mk_empty_array_with_capacity(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_unsigned_to_nat(32u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
lean_ctor_set(v___x_291_, 2, v___x_287_);
lean_ctor_set(v___x_291_, 3, v___x_287_);
lean_ctor_set_usize(v___x_291_, 4, v___x_286_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_box(1);
v___x_293_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_294_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; lean_object* v_env_301_; lean_object* v_options_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = lean_st_ref_get(v___y_298_);
v_env_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_ref(v_env_301_);
lean_dec(v___x_300_);
v_options_302_ = lean_ctor_get(v___y_297_, 2);
v___x_303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_302_);
v___x_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_305_, 0, v_env_301_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_304_);
lean_ctor_set(v___x_305_, 3, v_options_302_);
v___x_306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_msgData_296_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_ref_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_ref_317_ = lean_ctor_get(v___y_314_, 5);
v___x_318_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_313_, v___y_314_, v___y_315_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_ref_317_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_ref_317_);
lean_ctor_set(v___x_323_, 1, v_a_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 1);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_337_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_a_337_);
lean_dec_ref(v_x_333_);
v___x_338_ = l_Lean_stringToMessageData(v_a_337_);
v___x_339_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_338_, v___y_334_, v___y_335_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v_x_333_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v_x_333_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v_x_333_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 0);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(lean_object* v_typeName_353_, lean_object* v_constName_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_env_359_; uint8_t v___x_360_; 
v___x_358_ = lean_st_ref_get(v___y_356_);
v_env_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_358_);
lean_inc(v_constName_354_);
v___x_360_ = lean_has_compile_error(v_env_359_, v_constName_354_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v_options_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = lean_st_ref_get(v___y_356_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v_options_363_ = lean_ctor_get(v___y_355_, 2);
v___x_364_ = l_Lean_Environment_evalConstCheck___redArg(v_env_362_, v_options_363_, v_typeName_353_, v_constName_354_);
v___x_365_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_364_, v___y_355_, v___y_356_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; lean_object* v_env_368_; lean_object* v_options_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v___x_366_);
v___x_367_ = lean_st_ref_get(v___y_356_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v_options_369_ = lean_ctor_get(v___y_355_, 2);
v___x_370_ = l_Lean_Environment_evalConstCheck___redArg(v_env_368_, v_options_369_, v_typeName_353_, v_constName_354_);
v___x_371_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_370_, v___y_355_, v___y_356_);
return v___x_371_;
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_constName_354_);
lean_dec(v_typeName_353_);
v_a_372_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_366_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg___boxed(lean_object* v_typeName_380_, lean_object* v_constName_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_380_, v_constName_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object* v_name_393_, lean_object* v_declName_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3));
lean_inc(v_declName_394_);
v___x_399_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v___x_398_, v_declName_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_a_400_);
lean_ctor_set(v___x_404_, 1, v_name_393_);
lean_ctor_set(v___x_404_, 2, v_declName_394_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_declName_394_);
lean_dec(v_name_393_);
v_a_409_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_399_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_399_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object* v_name_417_, lean_object* v_declName_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(v_name_417_, v_declName_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(lean_object* v_00_u03b1_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___boxed(lean_object* v_00_u03b1_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(v_00_u03b1_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(lean_object* v_00_u03b1_433_, lean_object* v_typeName_434_, lean_object* v_constName_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_434_, v_constName_435_, v___y_436_, v___y_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_440_, lean_object* v_typeName_441_, lean_object* v_constName_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(v_00_u03b1_440_, v_typeName_441_, v_constName_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b1_447_, lean_object* v_x_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_448_, v___y_449_, v___y_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(v_00_u03b1_453_, v_x_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_460_, v___y_461_, v___y_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_465_, lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_465_, v_msg_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object* v_name_471_, lean_object* v_declName_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(v_name_471_, v_declName_472_, v_a_473_, v_a_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object* v_name_477_, lean_object* v_declName_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_name_477_, v_declName_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object* v_m_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_fst_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_fst_485_ = lean_ctor_get(v_x_484_, 0);
v___x_486_ = lean_box(0);
lean_inc(v_fst_485_);
v___x_487_ = l_Lean_Name_updatePrefix(v_fst_485_, v___x_486_);
v___x_488_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_487_, v_x_484_, v_m_483_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_489_, size_t v_i_490_, size_t v_stop_491_, lean_object* v_b_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_eq(v_i_490_, v_stop_491_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v_fst_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; 
v___x_494_ = lean_array_uget_borrowed(v_as_489_, v_i_490_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
v___x_496_ = lean_box(0);
lean_inc(v_fst_495_);
v___x_497_ = l_Lean_Name_updatePrefix(v_fst_495_, v___x_496_);
lean_inc(v___x_494_);
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_497_, v___x_494_, v_b_492_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_490_, v___x_499_);
v_i_490_ = v___x_500_;
v_b_492_ = v___x_498_;
goto _start;
}
else
{
return v_b_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_502_, lean_object* v_i_503_, lean_object* v_stop_504_, lean_object* v_b_505_){
_start:
{
size_t v_i_boxed_506_; size_t v_stop_boxed_507_; lean_object* v_res_508_; 
v_i_boxed_506_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_stop_boxed_507_ = lean_unbox_usize(v_stop_504_);
lean_dec(v_stop_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(v_as_502_, v_i_boxed_506_, v_stop_boxed_507_, v_b_505_);
lean_dec_ref(v_as_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(lean_object* v_as_509_, size_t v_i_510_, size_t v_stop_511_, lean_object* v_b_512_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_eq(v_i_510_, v_stop_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v_fst_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_514_ = lean_array_uget_borrowed(v_as_509_, v_i_510_);
v_fst_515_ = lean_ctor_get(v___x_514_, 0);
v___x_516_ = lean_box(0);
lean_inc(v_fst_515_);
v___x_517_ = l_Lean_Name_updatePrefix(v_fst_515_, v___x_516_);
lean_inc(v___x_514_);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_517_, v___x_514_, v_b_512_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_510_, v___x_519_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0_spec__0(v_as_509_, v___x_520_, v_stop_511_, v___x_518_);
return v___x_521_;
}
else
{
return v_b_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_522_, lean_object* v_i_523_, lean_object* v_stop_524_, lean_object* v_b_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v_as_522_, v_i_boxed_526_, v_stop_boxed_527_, v_b_525_);
lean_dec_ref(v_as_522_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(lean_object* v_as_529_, size_t v_i_530_, size_t v_stop_531_, lean_object* v_b_532_){
_start:
{
lean_object* v___y_534_; uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_eq(v_i_530_, v_stop_531_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_539_ = lean_array_uget_borrowed(v_as_529_, v_i_530_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_array_get_size(v___x_539_);
v___x_542_ = lean_nat_dec_lt(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
v___y_534_ = v_b_532_;
goto v___jp_533_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = lean_nat_dec_le(v___x_541_, v___x_541_);
if (v___x_543_ == 0)
{
if (v___x_542_ == 0)
{
v___y_534_ = v_b_532_;
goto v___jp_533_;
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_541_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v___x_539_, v___x_544_, v___x_545_, v_b_532_);
v___y_534_ = v___x_546_;
goto v___jp_533_;
}
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_541_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__0(v___x_539_, v___x_547_, v___x_548_, v_b_532_);
v___y_534_ = v___x_549_;
goto v___jp_533_;
}
}
}
else
{
return v_b_532_;
}
v___jp_533_:
{
size_t v___x_535_; size_t v___x_536_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_530_, v___x_535_);
v_i_530_ = v___x_536_;
v_b_532_ = v___y_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_550_, lean_object* v_i_551_, lean_object* v_stop_552_, lean_object* v_b_553_){
_start:
{
size_t v_i_boxed_554_; size_t v_stop_boxed_555_; lean_object* v_res_556_; 
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_stop_boxed_555_ = lean_unbox_usize(v_stop_552_);
lean_dec(v_stop_552_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_as_550_, v_i_boxed_554_, v_stop_boxed_555_, v_b_553_);
lean_dec_ref(v_as_550_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object* v_nss_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_558_ = lean_box(1);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v_nss_557_);
v___x_561_ = lean_nat_dec_lt(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
return v___x_558_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_le(v___x_560_, v___x_560_);
if (v___x_562_ == 0)
{
if (v___x_561_ == 0)
{
return v___x_558_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_560_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_nss_557_, v___x_563_, v___x_564_, v___x_558_);
return v___x_565_;
}
}
else
{
size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((size_t)0ULL);
v___x_567_ = lean_usize_of_nat(v___x_560_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2__spec__1(v_nss_557_, v___x_566_, v___x_567_, v___x_558_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(lean_object* v_nss_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(v_nss_569_);
lean_dec_ref(v_nss_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(lean_object* v_es_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_array_mk(v_es_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_));
v___x_591_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2____boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_();
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_ref_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_fileName_630_; lean_object* v_fileMap_631_; lean_object* v_options_632_; lean_object* v_currRecDepth_633_; lean_object* v_maxRecDepth_634_; lean_object* v_ref_635_; lean_object* v_currNamespace_636_; lean_object* v_openDecls_637_; lean_object* v_initHeartbeats_638_; lean_object* v_maxHeartbeats_639_; lean_object* v_quotContext_640_; lean_object* v_currMacroScope_641_; uint8_t v_diag_642_; lean_object* v_cancelTk_x3f_643_; uint8_t v_suppressElabErrors_644_; lean_object* v_inheritedTraceOptions_645_; lean_object* v_ref_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_fileName_630_ = lean_ctor_get(v___y_627_, 0);
v_fileMap_631_ = lean_ctor_get(v___y_627_, 1);
v_options_632_ = lean_ctor_get(v___y_627_, 2);
v_currRecDepth_633_ = lean_ctor_get(v___y_627_, 3);
v_maxRecDepth_634_ = lean_ctor_get(v___y_627_, 4);
v_ref_635_ = lean_ctor_get(v___y_627_, 5);
v_currNamespace_636_ = lean_ctor_get(v___y_627_, 6);
v_openDecls_637_ = lean_ctor_get(v___y_627_, 7);
v_initHeartbeats_638_ = lean_ctor_get(v___y_627_, 8);
v_maxHeartbeats_639_ = lean_ctor_get(v___y_627_, 9);
v_quotContext_640_ = lean_ctor_get(v___y_627_, 10);
v_currMacroScope_641_ = lean_ctor_get(v___y_627_, 11);
v_diag_642_ = lean_ctor_get_uint8(v___y_627_, sizeof(void*)*14);
v_cancelTk_x3f_643_ = lean_ctor_get(v___y_627_, 12);
v_suppressElabErrors_644_ = lean_ctor_get_uint8(v___y_627_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_645_ = lean_ctor_get(v___y_627_, 13);
v_ref_646_ = l_Lean_replaceRef(v_ref_625_, v_ref_635_);
lean_inc_ref(v_inheritedTraceOptions_645_);
lean_inc(v_cancelTk_x3f_643_);
lean_inc(v_currMacroScope_641_);
lean_inc(v_quotContext_640_);
lean_inc(v_maxHeartbeats_639_);
lean_inc(v_initHeartbeats_638_);
lean_inc(v_openDecls_637_);
lean_inc(v_currNamespace_636_);
lean_inc(v_maxRecDepth_634_);
lean_inc(v_currRecDepth_633_);
lean_inc_ref(v_options_632_);
lean_inc_ref(v_fileMap_631_);
lean_inc_ref(v_fileName_630_);
v___x_647_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_647_, 0, v_fileName_630_);
lean_ctor_set(v___x_647_, 1, v_fileMap_631_);
lean_ctor_set(v___x_647_, 2, v_options_632_);
lean_ctor_set(v___x_647_, 3, v_currRecDepth_633_);
lean_ctor_set(v___x_647_, 4, v_maxRecDepth_634_);
lean_ctor_set(v___x_647_, 5, v_ref_646_);
lean_ctor_set(v___x_647_, 6, v_currNamespace_636_);
lean_ctor_set(v___x_647_, 7, v_openDecls_637_);
lean_ctor_set(v___x_647_, 8, v_initHeartbeats_638_);
lean_ctor_set(v___x_647_, 9, v_maxHeartbeats_639_);
lean_ctor_set(v___x_647_, 10, v_quotContext_640_);
lean_ctor_set(v___x_647_, 11, v_currMacroScope_641_);
lean_ctor_set(v___x_647_, 12, v_cancelTk_x3f_643_);
lean_ctor_set(v___x_647_, 13, v_inheritedTraceOptions_645_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*14, v_diag_642_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*14 + 1, v_suppressElabErrors_644_);
v___x_648_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_626_, v___x_647_, v___y_628_);
lean_dec_ref(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_ref_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_649_, v_msg_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v_ref_649_);
return v_res_654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object* v_msg_676_, lean_object* v_declHint_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v_env_681_; uint8_t v___x_682_; 
v___x_680_ = lean_st_ref_get(v___y_678_);
v_env_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_env_681_);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_Name_isAnonymous(v_declHint_677_);
if (v___x_682_ == 0)
{
uint8_t v_isExporting_683_; 
v_isExporting_683_ = lean_ctor_get_uint8(v_env_681_, sizeof(void*)*8);
if (v_isExporting_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v_env_681_);
lean_dec(v_declHint_677_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_msg_676_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; uint8_t v___x_686_; 
lean_inc_ref(v_env_681_);
v___x_685_ = l_Lean_Environment_setExporting(v_env_681_, v___x_682_);
lean_inc(v_declHint_677_);
lean_inc_ref(v___x_685_);
v___x_686_ = l_Lean_Environment_contains(v___x_685_, v_declHint_677_, v_isExporting_683_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v___x_685_);
lean_dec_ref(v_env_681_);
lean_dec(v_declHint_677_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_msg_676_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_c_693_; lean_object* v___x_694_; 
v___x_688_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_689_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
v___x_690_ = l_Lean_Options_empty;
v___x_691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_691_, 0, v___x_685_);
lean_ctor_set(v___x_691_, 1, v___x_688_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
lean_inc(v_declHint_677_);
v___x_692_ = l_Lean_MessageData_ofConstName(v_declHint_677_, v___x_682_);
v_c_693_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_693_, 0, v___x_691_);
lean_ctor_set(v_c_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_681_, v_declHint_677_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref(v_env_681_);
lean_dec(v_declHint_677_);
v___x_695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_c_693_);
v___x_697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_Lean_MessageData_note(v___x_698_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v_msg_676_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
else
{
lean_object* v_val_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_737_; 
v_val_702_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_737_ == 0)
{
v___x_704_ = v___x_694_;
v_isShared_705_ = v_isSharedCheck_737_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_val_702_);
lean_dec(v___x_694_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_737_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_mod_709_; uint8_t v___x_710_; 
v___x_706_ = lean_box(0);
v___x_707_ = l_Lean_Environment_header(v_env_681_);
lean_dec_ref(v_env_681_);
v___x_708_ = l_Lean_EnvironmentHeader_moduleNames(v___x_707_);
v_mod_709_ = lean_array_get(v___x_706_, v___x_708_, v_val_702_);
lean_dec(v_val_702_);
lean_dec_ref(v___x_708_);
v___x_710_ = l_Lean_isPrivateName(v_declHint_677_);
lean_dec(v_declHint_677_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_c_693_);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_MessageData_ofName(v_mod_709_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_MessageData_note(v___x_718_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v_msg_676_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 0);
lean_ctor_set(v___x_704_, 0, v___x_720_);
v___x_722_ = v___x_704_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_c_693_);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_MessageData_ofName(v_mod_709_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_MessageData_note(v___x_731_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v_msg_676_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 0);
lean_ctor_set(v___x_704_, 0, v___x_733_);
v___x_735_ = v___x_704_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v_env_681_);
lean_dec(v_declHint_677_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v_msg_676_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msg_739_, lean_object* v_declHint_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_739_, v_declHint_740_, v___y_741_);
lean_dec(v___y_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_msg_744_, lean_object* v_declHint_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_759_; 
v___x_749_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_744_, v_declHint_745_, v___y_747_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_759_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_unknownIdentifierMessageTag;
v___x_755_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_a_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_msg_760_, lean_object* v_declHint_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_760_, v_declHint_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_766_, lean_object* v_msg_767_, lean_object* v_declHint_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_a_773_; lean_object* v___x_774_; 
v___x_772_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_767_, v_declHint_768_, v___y_769_, v___y_770_);
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_766_, v_a_773_, v___y_769_, v___y_770_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_775_, lean_object* v_msg_776_, lean_object* v_declHint_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_775_, v_msg_776_, v_declHint_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v_ref_775_);
return v_res_781_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_ref_788_, lean_object* v_constName_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_793_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_794_ = 0;
lean_inc(v_constName_789_);
v___x_795_ = l_Lean_MessageData_ofConstName(v_constName_789_, v___x_794_);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_788_, v___x_798_, v_constName_789_, v___y_790_, v___y_791_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_800_, lean_object* v_constName_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_800_, v_constName_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v_ref_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_constName_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_ref_810_; lean_object* v___x_811_; 
v_ref_810_ = lean_ctor_get(v___y_807_, 5);
v___x_811_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_810_, v_constName_806_, v___y_807_, v___y_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_constName_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v_env_822_; uint8_t v___x_823_; lean_object* v___x_824_; 
v___x_821_ = lean_st_ref_get(v___y_819_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = 0;
lean_inc(v_constName_817_);
v___x_824_ = l_Lean_Environment_find_x3f(v_env_822_, v_constName_817_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_817_, v___y_818_, v___y_819_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_constName_817_);
v_val_826_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_824_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v___x_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_val_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0___boxed(lean_object* v_constName_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(v_constName_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
if (lean_obj_tag(v_a_839_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_List_reverse___redArg(v_a_840_);
return v___x_841_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
v_head_842_ = lean_ctor_get(v_a_839_, 0);
v_tail_843_ = lean_ctor_get(v_a_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_845_ = v_a_839_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_tail_843_);
lean_inc(v_head_842_);
lean_dec(v_a_839_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = l_Lean_mkLevelParam(v_head_842_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_a_840_);
lean_ctor_set(v___x_845_, 0, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_840_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v_a_839_ = v_tail_843_;
v_a_840_ = v___x_849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_constName_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_env_858_; uint8_t v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_st_ref_get(v___y_855_);
v_env_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc_ref(v_env_858_);
lean_dec(v___x_857_);
v___x_859_ = 0;
lean_inc(v_constName_853_);
v___x_860_ = l_Lean_Environment_findConstVal_x3f(v_env_858_, v_constName_853_, v___x_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_853_, v___y_854_, v___y_855_);
return v___x_861_;
}
else
{
lean_object* v_val_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_constName_853_);
v_val_862_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_860_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_val_862_);
lean_dec(v___x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 0);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_val_862_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_constName_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
lean_inc(v_constName_875_);
v___x_879_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_891_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_891_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_levelParams_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_levelParams_884_ = lean_ctor_get(v_a_880_, 1);
lean_inc(v_levelParams_884_);
lean_dec(v_a_880_);
v___x_885_ = lean_box(0);
v___x_886_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_levelParams_884_, v___x_885_);
v___x_887_ = l_Lean_mkConst(v_constName_875_, v___x_886_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_887_);
v___x_889_ = v___x_882_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_constName_875_);
v_a_892_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_879_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_879_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_constName_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(v_constName_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object* v_t_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_infoState_909_; uint8_t v_enabled_910_; 
v___x_908_ = lean_st_ref_get(v___y_906_);
v_infoState_909_ = lean_ctor_get(v___x_908_, 7);
lean_inc_ref(v_infoState_909_);
lean_dec(v___x_908_);
v_enabled_910_ = lean_ctor_get_uint8(v_infoState_909_, sizeof(void*)*3);
lean_dec_ref(v_infoState_909_);
if (v_enabled_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_t_905_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v_infoState_914_; lean_object* v_env_915_; lean_object* v_nextMacroScope_916_; lean_object* v_ngen_917_; lean_object* v_auxDeclNGen_918_; lean_object* v_traceState_919_; lean_object* v_cache_920_; lean_object* v_messages_921_; lean_object* v_snapshotTasks_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_944_; 
v___x_913_ = lean_st_ref_take(v___y_906_);
v_infoState_914_ = lean_ctor_get(v___x_913_, 7);
v_env_915_ = lean_ctor_get(v___x_913_, 0);
v_nextMacroScope_916_ = lean_ctor_get(v___x_913_, 1);
v_ngen_917_ = lean_ctor_get(v___x_913_, 2);
v_auxDeclNGen_918_ = lean_ctor_get(v___x_913_, 3);
v_traceState_919_ = lean_ctor_get(v___x_913_, 4);
v_cache_920_ = lean_ctor_get(v___x_913_, 5);
v_messages_921_ = lean_ctor_get(v___x_913_, 6);
v_snapshotTasks_922_ = lean_ctor_get(v___x_913_, 8);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_944_ == 0)
{
v___x_924_ = v___x_913_;
v_isShared_925_ = v_isSharedCheck_944_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snapshotTasks_922_);
lean_inc(v_infoState_914_);
lean_inc(v_messages_921_);
lean_inc(v_cache_920_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_918_);
lean_inc(v_ngen_917_);
lean_inc(v_nextMacroScope_916_);
lean_inc(v_env_915_);
lean_dec(v___x_913_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_944_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
uint8_t v_enabled_926_; lean_object* v_assignment_927_; lean_object* v_lazyAssignment_928_; lean_object* v_trees_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_943_; 
v_enabled_926_ = lean_ctor_get_uint8(v_infoState_914_, sizeof(void*)*3);
v_assignment_927_ = lean_ctor_get(v_infoState_914_, 0);
v_lazyAssignment_928_ = lean_ctor_get(v_infoState_914_, 1);
v_trees_929_ = lean_ctor_get(v_infoState_914_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_infoState_914_);
if (v_isSharedCheck_943_ == 0)
{
v___x_931_ = v_infoState_914_;
v_isShared_932_ = v_isSharedCheck_943_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_trees_929_);
lean_inc(v_lazyAssignment_928_);
lean_inc(v_assignment_927_);
lean_dec(v_infoState_914_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_943_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = l_Lean_PersistentArray_push___redArg(v_trees_929_, v_t_905_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_assignment_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_lazyAssignment_928_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v___x_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, sizeof(void*)*3, v_enabled_926_);
v___x_935_ = v_reuseFailAlloc_942_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 7, v___x_935_);
v___x_937_ = v___x_924_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_env_915_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_nextMacroScope_916_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_ngen_917_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_auxDeclNGen_918_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_traceState_919_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_cache_920_);
lean_ctor_set(v_reuseFailAlloc_941_, 6, v_messages_921_);
lean_ctor_set(v_reuseFailAlloc_941_, 7, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 8, v_snapshotTasks_922_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_st_ref_set(v___y_906_, v___x_937_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_t_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_945_, v___y_946_);
lean_dec(v___y_946_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(32u);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_952_ = ((size_t)5ULL);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_unsigned_to_nat(32u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__0);
v___x_957_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_953_);
lean_ctor_set(v___x_957_, 3, v___x_953_);
lean_ctor_set_usize(v___x_957_, 4, v___x_952_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_t_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_infoState_963_; uint8_t v_enabled_964_; 
v___x_962_ = lean_st_ref_get(v___y_960_);
v_infoState_963_ = lean_ctor_get(v___x_962_, 7);
lean_inc_ref(v_infoState_963_);
lean_dec(v___x_962_);
v_enabled_964_ = lean_ctor_get_uint8(v_infoState_963_, sizeof(void*)*3);
lean_dec_ref(v_infoState_963_);
if (v_enabled_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_t_958_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___closed__1);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v_t_958_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v___x_968_, v___y_960_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_t_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(v_t_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(lean_object* v_stx_975_, lean_object* v_n_976_, lean_object* v_expectedType_x3f_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__2(v_n_976_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_stx_975_);
v___x_985_ = l_Lean_LocalContext_empty;
v___x_986_ = 0;
v___x_987_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_987_, 0, v___x_984_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v_expectedType_x3f_977_);
lean_ctor_set(v___x_987_, 3, v_a_982_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*4, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*4 + 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3(v___x_988_, v___y_978_, v___y_979_);
return v___x_989_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_expectedType_x3f_977_);
lean_dec(v_stx_975_);
v_a_990_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_981_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_981_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_998_, lean_object* v_n_999_, lean_object* v_expectedType_x3f_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(v_stx_998_, v_n_999_, v_expectedType_x3f_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1004_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1005_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static uint64_t _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1022_; uint64_t v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1023_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_uint64_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1025_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1026_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set_uint64(v___x_1026_, sizeof(void*)*1, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1027_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1031_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
lean_ctor_set(v___x_1031_, 3, v___x_1030_);
lean_ctor_set(v___x_1031_, 4, v___x_1030_);
lean_ctor_set(v___x_1031_, 5, v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
lean_ctor_set(v___x_1033_, 3, v___x_1032_);
lean_ctor_set(v___x_1033_, 4, v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_decl_1059_, lean_object* v_stx_1060_, uint8_t v_kind_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v_dflt_1067_; lean_object* v___y_1069_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; uint8_t v_a_1103_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1199_; lean_object* v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1206_; lean_object* v___y_1207_; uint8_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = l_Lean_Syntax_getArg(v_stx_1060_, v___x_1065_);
v_dflt_1067_ = l_Lean_Syntax_isNone(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_instBEqAttributeKind_beq(v_kind_1061_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_stx_1060_);
lean_dec(v_decl_1059_);
lean_dec(v___x_1058_);
lean_dec(v___x_1057_);
lean_dec(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v___x_1239_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1240_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1239_, v___y_1062_, v___y_1063_);
return v___x_1240_;
}
else
{
goto v___jp_1211_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v_env_1071_; lean_object* v_nextMacroScope_1072_; lean_object* v_ngen_1073_; lean_object* v_auxDeclNGen_1074_; lean_object* v_traceState_1075_; lean_object* v_messages_1076_; lean_object* v_infoState_1077_; lean_object* v_snapshotTasks_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1095_; 
v___x_1070_ = lean_st_ref_take(v___y_1069_);
v_env_1071_ = lean_ctor_get(v___x_1070_, 0);
v_nextMacroScope_1072_ = lean_ctor_get(v___x_1070_, 1);
v_ngen_1073_ = lean_ctor_get(v___x_1070_, 2);
v_auxDeclNGen_1074_ = lean_ctor_get(v___x_1070_, 3);
v_traceState_1075_ = lean_ctor_get(v___x_1070_, 4);
v_messages_1076_ = lean_ctor_get(v___x_1070_, 6);
v_infoState_1077_ = lean_ctor_get(v___x_1070_, 7);
v_snapshotTasks_1078_ = lean_ctor_get(v___x_1070_, 8);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1070_, 5);
lean_dec(v_unused_1096_);
v___x_1080_ = v___x_1070_;
v_isShared_1081_ = v_isSharedCheck_1095_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snapshotTasks_1078_);
lean_inc(v_infoState_1077_);
lean_inc(v_messages_1076_);
lean_inc(v_traceState_1075_);
lean_inc(v_auxDeclNGen_1074_);
lean_inc(v_ngen_1073_);
lean_inc(v_nextMacroScope_1072_);
lean_inc(v_env_1071_);
lean_dec(v___x_1070_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1095_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_toEnvExtension_1083_; lean_object* v_asyncMode_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1082_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_1083_ = lean_ctor_get(v___x_1082_, 0);
v_asyncMode_1084_ = lean_ctor_get(v_toEnvExtension_1083_, 2);
v___x_1085_ = lean_box(v_dflt_1067_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_decl_1059_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1082_, v_env_1071_, v___x_1086_, v_asyncMode_1084_, v___x_1052_);
v___x_1088_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 5, v___x_1088_);
lean_ctor_set(v___x_1080_, 0, v___x_1087_);
v___x_1090_ = v___x_1080_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_nextMacroScope_1072_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_ngen_1073_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_auxDeclNGen_1074_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_traceState_1075_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1094_, 6, v_messages_1076_);
lean_ctor_set(v_reuseFailAlloc_1094_, 7, v_infoState_1077_);
lean_ctor_set(v_reuseFailAlloc_1094_, 8, v_snapshotTasks_1078_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_st_ref_set(v___y_1069_, v___x_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
v___jp_1097_:
{
if (v_a_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1052_);
v___x_1104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1105_ = l_Lean_MessageData_ofConstName(v_decl_1059_, v___y_1102_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_MessageData_ofConstName(v___y_1100_, v___y_1102_);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_MessageData_ofExpr(v___y_1098_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1104_);
v___x_1116_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1115_, v___y_1101_, v___y_1099_);
return v___x_1116_;
}
else
{
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1098_);
v___y_1069_ = v___y_1099_;
goto v___jp_1068_;
}
}
v___jp_1117_:
{
lean_object* v___x_1120_; 
lean_inc(v_decl_1059_);
v___x_1120_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0(v_decl_1059_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
lean_inc_ref(v___x_1055_);
v___x_1122_ = l_Lean_Name_mkStr4(v___x_1053_, v___x_1054_, v___x_1055_, v___x_1055_);
v___x_1123_ = 0;
v___x_1124_ = 1;
v___x_1125_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1126_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1127_ = lean_unsigned_to_nat(32u);
v___x_1128_ = lean_mk_empty_array_with_capacity(v___x_1127_);
v___x_1129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_1130_ = ((size_t)5ULL);
lean_inc_n(v___x_1056_, 6);
v___x_1131_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1128_);
lean_ctor_set(v___x_1131_, 2, v___x_1056_);
lean_ctor_set(v___x_1131_, 3, v___x_1056_);
lean_ctor_set_usize(v___x_1131_, 4, v___x_1130_);
v___x_1132_ = lean_box(1);
lean_inc_ref(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1126_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
v___x_1134_ = lean_mk_empty_array_with_capacity(v___x_1056_);
v___x_1135_ = lean_box(0);
lean_inc(v___x_1057_);
v___x_1136_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1136_, 0, v___x_1125_);
lean_ctor_set(v___x_1136_, 1, v___x_1057_);
lean_ctor_set(v___x_1136_, 2, v___x_1133_);
lean_ctor_set(v___x_1136_, 3, v___x_1134_);
lean_ctor_set(v___x_1136_, 4, v___x_1135_);
lean_ctor_set(v___x_1136_, 5, v___x_1056_);
lean_ctor_set(v___x_1136_, 6, v___x_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7, v___x_1123_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 1, v___x_1123_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 2, v___x_1123_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 3, v___x_1124_);
v___x_1137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1056_);
lean_ctor_set(v___x_1137_, 1, v___x_1056_);
lean_ctor_set(v___x_1137_, 2, v___x_1056_);
lean_ctor_set(v___x_1137_, 3, v___x_1056_);
lean_ctor_set(v___x_1137_, 4, v___x_1126_);
lean_ctor_set(v___x_1137_, 5, v___x_1126_);
lean_ctor_set(v___x_1137_, 6, v___x_1126_);
lean_ctor_set(v___x_1137_, 7, v___x_1126_);
lean_ctor_set(v___x_1137_, 8, v___x_1126_);
lean_ctor_set(v___x_1137_, 9, v___x_1126_);
v___x_1138_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1139_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1057_);
lean_ctor_set(v___x_1140_, 3, v___x_1131_);
lean_ctor_set(v___x_1140_, 4, v___x_1139_);
v___x_1141_ = lean_st_mk_ref(v___x_1140_);
v___x_1142_ = l_Lean_ConstantInfo_type(v_a_1121_);
lean_dec(v_a_1121_);
v___x_1143_ = lean_box(0);
lean_inc(v___x_1122_);
v___x_1144_ = l_Lean_mkConst(v___x_1122_, v___x_1143_);
lean_inc_ref(v___x_1142_);
v___x_1145_ = l_Lean_Meta_isExprDefEq(v___x_1142_, v___x_1144_, v___x_1136_, v___x_1141_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___x_1136_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = lean_st_ref_get(v___x_1141_);
lean_dec(v___x_1141_);
lean_dec(v___x_1147_);
v___x_1148_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
v___y_1098_ = v___x_1142_;
v___y_1099_ = v___y_1119_;
v___y_1100_ = v___x_1122_;
v___y_1101_ = v___y_1118_;
v___y_1102_ = v___x_1123_;
v_a_1103_ = v___x_1148_;
goto v___jp_1097_;
}
else
{
lean_dec(v___x_1141_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1149_; uint8_t v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1145_);
v___x_1150_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
v___y_1098_ = v___x_1142_;
v___y_1099_ = v___y_1119_;
v___y_1100_ = v___x_1122_;
v___y_1101_ = v___y_1118_;
v___y_1102_ = v___x_1123_;
v_a_1103_ = v___x_1150_;
goto v___jp_1097_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v___x_1142_);
lean_dec(v___x_1122_);
lean_dec(v_decl_1059_);
lean_dec(v___x_1052_);
v_a_1151_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1145_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1145_);
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
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_decl_1059_);
lean_dec(v___x_1057_);
lean_dec(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v_a_1159_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1120_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1120_);
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
v___jp_1167_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc_ref(v___y_1171_);
v___x_1172_ = l_Lean_stringToMessageData(v___y_1171_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___y_1168_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1173_, v___y_1170_, v___y_1169_);
return v___x_1174_;
}
v___jp_1175_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_inc_ref(v___y_1180_);
v___x_1181_ = l_Lean_stringToMessageData(v___y_1180_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1177_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
if (v___y_1178_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___y_1168_ = v___x_1182_;
v___y_1169_ = v___y_1176_;
v___y_1170_ = v___y_1179_;
v___y_1171_ = v___x_1183_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___y_1168_ = v___x_1182_;
v___y_1169_ = v___y_1176_;
v___y_1170_ = v___y_1179_;
v___y_1171_ = v___x_1184_;
goto v___jp_1167_;
}
}
v___jp_1185_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1192_ = l_Lean_MessageData_ofConstName(v_decl_1059_, v___y_1190_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
if (v___y_1186_ == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___x_1195_;
v___y_1178_ = v___y_1188_;
v___y_1179_ = v___y_1189_;
v___y_1180_ = v___x_1196_;
goto v___jp_1175_;
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___x_1195_;
v___y_1178_ = v___y_1188_;
v___y_1179_ = v___y_1189_;
v___y_1180_ = v___x_1197_;
goto v___jp_1175_;
}
}
v___jp_1198_:
{
lean_object* v___x_1202_; lean_object* v_env_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_st_ref_get(v___y_1199_);
v_env_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_ref(v_env_1203_);
lean_dec(v___x_1202_);
lean_inc(v_decl_1059_);
v___x_1204_ = l_Lean_isMarkedMeta(v_env_1203_, v_decl_1059_);
if (v___y_1201_ == 0)
{
lean_dec(v___x_1057_);
lean_dec(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v___y_1186_ = v___y_1201_;
v___y_1187_ = v___y_1199_;
v___y_1188_ = v___x_1204_;
v___y_1189_ = v___y_1200_;
v___y_1190_ = v___y_1201_;
goto v___jp_1185_;
}
else
{
if (v___x_1204_ == 0)
{
lean_dec(v___x_1057_);
lean_dec(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v___y_1186_ = v___y_1201_;
v___y_1187_ = v___y_1199_;
v___y_1188_ = v___x_1204_;
v___y_1189_ = v___y_1200_;
v___y_1190_ = v___x_1204_;
goto v___jp_1185_;
}
else
{
v___y_1118_ = v___y_1200_;
v___y_1119_ = v___y_1199_;
goto v___jp_1117_;
}
}
}
v___jp_1205_:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Lean_isPrivateName(v_decl_1059_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 1;
v___y_1199_ = v___y_1207_;
v___y_1200_ = v___y_1206_;
v___y_1201_ = v___x_1209_;
goto v___jp_1198_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
v___y_1199_ = v___y_1207_;
v___y_1200_ = v___y_1206_;
v___y_1201_ = v___x_1210_;
goto v___jp_1198_;
}
}
v___jp_1211_:
{
lean_object* v___x_1212_; lean_object* v_env_1213_; lean_object* v___x_1214_; lean_object* v_toEnvExtension_1215_; lean_object* v_asyncMode_1216_; lean_object* v_shortName_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1212_ = lean_st_ref_get(v___y_1063_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_env_1213_);
lean_dec(v___x_1212_);
v___x_1214_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_1215_ = lean_ctor_get(v___x_1214_, 0);
v_asyncMode_1216_ = lean_ctor_get(v_toEnvExtension_1215_, 2);
lean_inc_n(v___x_1052_, 2);
lean_inc(v_decl_1059_);
v_shortName_1217_ = l_Lean_Name_updatePrefix(v_decl_1059_, v___x_1052_);
v___x_1218_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1058_, v___x_1214_, v_env_1213_, v_asyncMode_1216_, v___x_1052_);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1218_, v_shortName_1217_);
lean_dec(v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 1)
{
lean_object* v_val_1220_; lean_object* v_fst_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_decl_1059_);
lean_dec(v___x_1057_);
lean_dec(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v_val_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_val_1220_);
lean_dec_ref(v___x_1219_);
v_fst_1221_ = lean_ctor_get(v_val_1220_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_val_1220_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_val_1220_, 1);
lean_dec(v_unused_1236_);
v___x_1223_ = v_val_1220_;
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_fst_1221_);
lean_dec(v_val_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1(v_stx_1060_, v_fst_1221_, v___x_1225_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1226_);
v___x_1227_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1228_ = l_Lean_MessageData_ofName(v_shortName_1217_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 7);
lean_ctor_set(v___x_1223_, 1, v___x_1228_);
lean_ctor_set(v___x_1223_, 0, v___x_1227_);
v___x_1230_ = v___x_1223_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1232_, v___y_1062_, v___y_1063_);
return v___x_1233_;
}
}
else
{
lean_del_object(v___x_1223_);
lean_dec(v_shortName_1217_);
return v___x_1226_;
}
}
}
else
{
lean_dec(v___x_1219_);
lean_dec(v_shortName_1217_);
lean_dec(v_stx_1060_);
v___y_1206_ = v___y_1062_;
v___y_1207_ = v___y_1063_;
goto v___jp_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v_decl_1248_, lean_object* v_stx_1249_, lean_object* v_kind_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
uint8_t v_kind_boxed_1254_; lean_object* v_res_1255_; 
v_kind_boxed_1254_ = lean_unbox(v_kind_1250_);
v_res_1255_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(v___x_1241_, v___x_1242_, v___x_1243_, v___x_1244_, v___x_1245_, v___x_1246_, v___x_1247_, v_decl_1248_, v_stx_1249_, v_kind_boxed_1254_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1255_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(lean_object* v___x_1262_, lean_object* v_decl_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1267_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1268_ = l_Lean_MessageData_ofName(v___x_1262_);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1271_, v___y_1264_, v___y_1265_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object* v___x_1273_, lean_object* v_decl_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(v___x_1273_, v_decl_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v_decl_1274_);
return v_res_1278_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_unsigned_to_nat(3913590394u);
v___x_1336_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1337_ = l_Lean_Name_num___override(v___x_1336_, v___x_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1340_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1341_ = l_Lean_Name_str___override(v___x_1340_, v___x_1339_);
return v___x_1341_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1344_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1345_ = l_Lean_Name_str___override(v___x_1344_, v___x_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(2u);
v___x_1347_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1348_ = l_Lean_Name_num___override(v___x_1347_, v___x_1346_);
return v___x_1348_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1354_ = 0;
v___x_1355_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1356_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1357_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1358_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v___x_1355_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*3, v___x_1354_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___f_1359_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___f_1360_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_));
v___x_1361_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___f_1360_);
lean_ctor_set(v___x_1362_, 2, v___f_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_);
v___x_1365_ = l_Lean_registerBuiltinAttribute(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2____boxed(lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_();
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_constName_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1374_, v_constName_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object* v_t_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_1380_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object* v_t_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__1_spec__3_spec__7(v_t_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1390_, lean_object* v_ref_1391_, lean_object* v_constName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_1391_, v_constName_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_ref_1398_, lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_1397_, v_ref_1398_, v_constName_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_ref_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1404_, lean_object* v_ref_1405_, lean_object* v_msg_1406_, lean_object* v_declHint_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1405_, v_msg_1406_, v_declHint_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1412_, v_ref_1413_, v_msg_1414_, v_declHint_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v_ref_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(lean_object* v_msg_1420_, lean_object* v_declHint_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_1420_, v_declHint_1421_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_1426_, lean_object* v_declHint_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(v_msg_1426_, v_declHint_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b1_1432_, lean_object* v_ref_1433_, lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1433_, v_msg_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_1439_, v_ref_1440_, v_msg_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v_ref_1440_);
return v_res_1445_;
}
}
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_4146909459____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_EnvLinter_envLinterExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_EnvLinter_envLinterExt);
lean_dec_ref(res);
res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3913590394____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_EnvLinter_Nolint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_EnvLinter_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

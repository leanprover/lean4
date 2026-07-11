// Lean compiler output
// Module: Lean.Elab.DeprecatedArg
// Imports: public import Lean.EnvExtension public import Lean.Message import Lean.Elab.Term
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(34, 76, 221, 236, 220, 4, 80, 27)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "if true, generate deprecation warnings and errors for deprecated parameters"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 137, 139, 132, 156, 105, 17, 87)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 255, 51, 83, 51, 207, 102, 168)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 17, 141, 46, 239, 35, 224, 220)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_linter_deprecated_arg;
static const lean_ctor_object l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deprecatedArgExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 157, 100, 72, 87, 251, 253, 102)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedArgExt;
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__0 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__1;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parameter `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__2 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__3;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__4 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__5;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__6 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__7;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` has been deprecated, use `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__8 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__9;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__10 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 138, .m_capacity = 138, .m_length = 137, .m_data = "`[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is still a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`; rename it to `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` is not a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`; remove it before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Invalid `[deprecated_arg]` attribute syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DeprecatedArg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 168, 92, 104, 219, 200, 6, 160)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 45, 177, 228, 29, 219, 125, 116)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 25, 22, 75, 158, 128, 229, 101)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(107, 124, 96, 157, 76, 98, 131, 88)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 213, 49, 250, 165, 149, 52, 239)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 47, 237, 141, 165, 175, 79, 67)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 84, 26, 57, 180, 177, 26, 182)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(140, 241, 34, 119, 16, 121, 80, 72)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 144, 188, 92, 44, 216, 0, 99)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecated_arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 6, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 182, 86, 230, 168, 246, 164, 173)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark a parameter as deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object* v_s_67_, lean_object* v_e_68_){
_start:
{
lean_object* v_declName_69_; lean_object* v_oldArg_70_; lean_object* v___y_72_; lean_object* v___x_75_; 
v_declName_69_ = lean_ctor_get(v_e_68_, 0);
lean_inc(v_declName_69_);
v_oldArg_70_ = lean_ctor_get(v_e_68_, 1);
lean_inc(v_oldArg_70_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_67_, v_declName_69_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
v___y_72_ = v___x_76_;
goto v___jp_71_;
}
else
{
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_75_, 1);
v___y_72_ = v_val_77_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v_inner_73_; lean_object* v___x_74_; 
v_inner_73_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_oldArg_70_, v_e_68_, v___y_72_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_69_, v_inner_73_, v_s_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object* v_es_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_array_mk(v_es_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_85_);
v___x_86_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(v_b_83_, v___x_85_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_81_, v___x_87_);
v_i_81_ = v___x_88_;
v_b_83_ = v___x_86_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
lean_object* v___y_102_; uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_107_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_get_size(v___x_107_);
v___x_110_ = lean_nat_dec_lt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
v___y_102_ = v_b_100_;
goto v___jp_101_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_le(v___x_109_, v___x_109_);
if (v___x_111_ == 0)
{
if (v___x_110_ == 0)
{
v___y_102_ = v_b_100_;
goto v___jp_101_;
}
else
{
size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((size_t)0ULL);
v___x_113_ = lean_usize_of_nat(v___x_109_);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_107_, v___x_112_, v___x_113_, v_b_100_);
v___y_102_ = v___x_114_;
goto v___jp_101_;
}
}
else
{
size_t v___x_115_; size_t v___x_116_; lean_object* v___x_117_; 
v___x_115_ = ((size_t)0ULL);
v___x_116_ = lean_usize_of_nat(v___x_109_);
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_107_, v___x_115_, v___x_116_, v_b_100_);
v___y_102_ = v___x_117_;
goto v___jp_101_;
}
}
}
else
{
return v_b_100_;
}
v___jp_101_:
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_98_, v___x_103_);
v_i_98_ = v___x_104_;
v_b_100_ = v___y_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_118_, lean_object* v_i_119_, lean_object* v_stop_120_, lean_object* v_b_121_){
_start:
{
size_t v_i_boxed_122_; size_t v_stop_boxed_123_; lean_object* v_res_124_; 
v_i_boxed_122_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_120_);
lean_dec(v_stop_120_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_118_, v_i_boxed_122_, v_stop_boxed_123_, v_b_121_);
lean_dec_ref(v_as_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object* v_initState_125_, lean_object* v_as_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_array_get_size(v_as_126_);
v___x_129_ = lean_nat_dec_lt(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
return v_initState_125_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_le(v___x_128_, v___x_128_);
if (v___x_130_ == 0)
{
if (v___x_129_ == 0)
{
return v_initState_125_;
}
else
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_128_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_126_, v___x_131_, v___x_132_, v_initState_125_);
return v___x_133_;
}
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_128_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_126_, v___x_134_, v___x_135_, v_initState_125_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_137_, lean_object* v_as_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_137_, v_as_138_);
lean_dec_ref(v_as_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_));
v___x_158_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object* v_env_161_, lean_object* v_declName_162_, lean_object* v_argName_163_){
_start:
{
lean_object* v___x_164_; lean_object* v_toEnvExtension_165_; lean_object* v_asyncMode_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_165_ = lean_ctor_get(v___x_164_, 0);
v_asyncMode_166_ = lean_ctor_get(v_toEnvExtension_165_, 2);
v___x_167_ = lean_box(1);
v___x_168_ = lean_box(0);
v___x_169_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_167_, v___x_164_, v_env_161_, v_asyncMode_166_, v___x_168_);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_169_, v_declName_162_);
lean_dec(v___x_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_170_, 1);
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_172_, v_argName_163_);
lean_dec(v_val_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object* v_env_174_, lean_object* v_declName_175_, lean_object* v_argName_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_174_, v_declName_175_, v_argName_176_);
lean_dec(v_argName_176_);
lean_dec(v_declName_175_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__0));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__2));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__4));
v___x_186_ = l_Lean_stringToMessageData(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__6));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__8));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__10));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object* v_entry_196_){
_start:
{
lean_object* v_declName_197_; lean_object* v_oldArg_198_; lean_object* v_newArg_x3f_199_; lean_object* v_text_x3f_200_; lean_object* v___y_202_; 
v_declName_197_ = lean_ctor_get(v_entry_196_, 0);
lean_inc(v_declName_197_);
v_oldArg_198_ = lean_ctor_get(v_entry_196_, 1);
lean_inc(v_oldArg_198_);
v_newArg_x3f_199_ = lean_ctor_get(v_entry_196_, 2);
lean_inc(v_newArg_x3f_199_);
v_text_x3f_200_ = lean_ctor_get(v_entry_196_, 3);
lean_inc(v_text_x3f_200_);
lean_dec_ref(v_entry_196_);
if (lean_obj_tag(v_newArg_x3f_199_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_208_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_209_ = l_Lean_MessageData_ofName(v_oldArg_198_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = 0;
v___x_214_ = l_Lean_MessageData_ofConstName(v_declName_197_, v___x_213_);
v___x_215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__7, &l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___y_202_ = v___x_217_;
goto v___jp_201_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_val_218_ = lean_ctor_get(v_newArg_x3f_199_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_newArg_x3f_199_, 1);
v___x_219_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_220_ = l_Lean_MessageData_ofName(v_oldArg_198_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = l_Lean_MessageData_ofConstName(v_declName_197_, v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__9, &l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = l_Lean_MessageData_ofName(v_val_218_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__11, &l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___y_202_ = v___x_232_;
goto v___jp_201_;
}
v___jp_201_:
{
if (lean_obj_tag(v_text_x3f_200_) == 0)
{
return v___y_202_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_val_203_ = lean_ctor_get(v_text_x3f_200_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v_text_x3f_200_, 1);
v___x_204_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__1, &l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1);
v___x_205_ = l_Lean_stringToMessageData(v_val_203_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(lean_object* v_k_233_, lean_object* v_b_234_, lean_object* v_c_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
lean_inc(v___y_237_);
lean_inc_ref(v___y_236_);
v___x_241_ = lean_apply_7(v_k_233_, v_b_234_, v_c_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, lean_box(0));
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(lean_object* v_k_242_, lean_object* v_b_243_, lean_object* v_c_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(v_k_242_, v_b_243_, v_c_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(lean_object* v_type_251_, lean_object* v_k_252_, uint8_t v_cleanupAnnotations_253_, uint8_t v_whnfType_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___f_260_; lean_object* v___x_261_; 
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_260_, 0, v_k_252_);
v___x_261_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_251_, v___f_260_, v_cleanupAnnotations_253_, v_whnfType_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_a_270_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_261_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_261_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_type_278_, lean_object* v_k_279_, lean_object* v_cleanupAnnotations_280_, lean_object* v_whnfType_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_287_; uint8_t v_whnfType_boxed_288_; lean_object* v_res_289_; 
v_cleanupAnnotations_boxed_287_ = lean_unbox(v_cleanupAnnotations_280_);
v_whnfType_boxed_288_ = lean_unbox(v_whnfType_281_);
v_res_289_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_278_, v_k_279_, v_cleanupAnnotations_boxed_287_, v_whnfType_boxed_288_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_290_, lean_object* v_type_291_, lean_object* v_k_292_, uint8_t v_cleanupAnnotations_293_, uint8_t v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_291_, v_k_292_, v_cleanupAnnotations_293_, v_whnfType_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_301_, lean_object* v_type_302_, lean_object* v_k_303_, lean_object* v_cleanupAnnotations_304_, lean_object* v_whnfType_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_311_; uint8_t v_whnfType_boxed_312_; lean_object* v_res_313_; 
v_cleanupAnnotations_boxed_311_ = lean_unbox(v_cleanupAnnotations_304_);
v_whnfType_boxed_312_ = lean_unbox(v_whnfType_305_);
v_res_313_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(v_00_u03b1_301_, v_type_302_, v_k_303_, v_cleanupAnnotations_boxed_311_, v_whnfType_boxed_312_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(size_t v_sz_314_, size_t v_i_315_, lean_object* v_bs_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_315_, v_sz_314_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_bs_316_);
return v___x_322_;
}
else
{
lean_object* v_v_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_v_323_ = lean_array_uget_borrowed(v_bs_316_, v_i_315_);
v___x_324_ = l_Lean_Expr_fvarId_x21(v_v_323_);
v___x_325_ = l_Lean_FVarId_getDecl___redArg(v___x_324_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_bs_x27_328_; lean_object* v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = lean_unsigned_to_nat(0u);
v_bs_x27_328_ = lean_array_uset(v_bs_316_, v_i_315_, v___x_327_);
v___x_329_ = l_Lean_LocalDecl_userName(v_a_326_);
lean_dec(v_a_326_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_315_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_328_, v_i_315_, v___x_329_);
v_i_315_ = v___x_331_;
v_bs_316_ = v___x_332_;
goto _start;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_bs_316_);
v_a_334_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_325_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_bs_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
size_t v_sz_boxed_349_; size_t v_i_boxed_350_; lean_object* v_res_351_; 
v_sz_boxed_349_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_350_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_boxed_349_, v_i_boxed_350_, v_bs_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v_xs_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
size_t v_sz_359_; size_t v___x_360_; lean_object* v___x_361_; 
v_sz_359_ = lean_array_size(v_xs_352_);
v___x_360_ = ((size_t)0ULL);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_359_, v___x_360_, v_xs_352_, v___y_354_, v___y_356_, v___y_357_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v_xs_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v_xs_362_, v_x_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v_x_363_);
return v_res_369_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(lean_object* v_oldArg_370_, lean_object* v_as_371_, size_t v_i_372_, size_t v_stop_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = lean_usize_dec_eq(v_i_372_, v_stop_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_array_uget_borrowed(v_as_371_, v_i_372_);
v___x_376_ = lean_name_eq(v___x_375_, v_oldArg_370_);
if (v___x_376_ == 0)
{
size_t v___x_377_; size_t v___x_378_; 
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_372_, v___x_377_);
v_i_372_ = v___x_378_;
goto _start;
}
else
{
return v___x_376_;
}
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2___boxed(lean_object* v_oldArg_381_, lean_object* v_as_382_, lean_object* v_i_383_, lean_object* v_stop_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; uint8_t v_res_387_; lean_object* v_r_388_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_384_);
lean_dec(v_stop_384_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_oldArg_381_, v_as_382_, v_i_boxed_385_, v_stop_boxed_386_);
lean_dec_ref(v_as_382_);
lean_dec(v_oldArg_381_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_389_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_ctor_set(v___x_394_, 3, v___x_393_);
lean_ctor_set(v___x_394_, 4, v___x_392_);
lean_ctor_set(v___x_394_, 5, v___x_392_);
lean_ctor_set(v___x_394_, 6, v___x_392_);
lean_ctor_set(v___x_394_, 7, v___x_392_);
lean_ctor_set(v___x_394_, 8, v___x_392_);
lean_ctor_set(v___x_394_, 9, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(32u);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_399_);
lean_ctor_set(v___x_403_, 3, v___x_399_);
lean_ctor_set_usize(v___x_403_, 4, v___x_398_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_box(1);
v___x_405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_406_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_404_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_429_, lean_object* v_declHint_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; lean_object* v_env_434_; uint8_t v___y_436_; uint8_t v___x_492_; uint8_t v___x_493_; 
v___x_433_ = lean_st_ref_get(v___y_431_);
v_env_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_env_434_);
lean_dec(v___x_433_);
v___x_492_ = l_Lean_Name_isAnonymous(v_declHint_430_);
v___x_493_ = lean_bool_not(v___x_492_);
if (v___x_493_ == 0)
{
v___y_436_ = v___x_493_;
goto v___jp_435_;
}
else
{
uint8_t v_isExporting_494_; 
v_isExporting_494_ = lean_ctor_get_uint8(v_env_434_, sizeof(void*)*8);
v___y_436_ = v_isExporting_494_;
goto v___jp_435_;
}
v___jp_435_:
{
if (v___y_436_ == 0)
{
lean_object* v___x_437_; 
lean_dec_ref(v_env_434_);
lean_dec(v_declHint_430_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_msg_429_);
return v___x_437_;
}
else
{
uint8_t v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = 0;
lean_inc_ref(v_env_434_);
v___x_439_ = l_Lean_Environment_setExporting(v_env_434_, v___x_438_);
lean_inc(v_declHint_430_);
lean_inc_ref(v___x_439_);
v___x_440_ = l_Lean_Environment_contains(v___x_439_, v_declHint_430_, v___y_436_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_dec_ref(v___x_439_);
lean_dec_ref(v_env_434_);
lean_dec(v_declHint_430_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_msg_429_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_c_447_; lean_object* v___x_448_; 
v___x_442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_443_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_444_ = l_Lean_Options_empty;
v___x_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_439_);
lean_ctor_set(v___x_445_, 1, v___x_442_);
lean_ctor_set(v___x_445_, 2, v___x_443_);
lean_ctor_set(v___x_445_, 3, v___x_444_);
lean_inc(v_declHint_430_);
v___x_446_ = l_Lean_MessageData_ofConstName(v_declHint_430_, v___x_438_);
v_c_447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_447_, 0, v___x_445_);
lean_ctor_set(v_c_447_, 1, v___x_446_);
v___x_448_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_434_, v_declHint_430_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref(v_env_434_);
lean_dec(v_declHint_430_);
v___x_449_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_c_447_);
v___x_451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = l_Lean_MessageData_note(v___x_452_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v_msg_429_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_491_; 
v_val_456_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_491_ == 0)
{
v___x_458_ = v___x_448_;
v_isShared_459_ = v_isSharedCheck_491_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v___x_448_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_491_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_mod_463_; uint8_t v___x_464_; 
v___x_460_ = lean_box(0);
v___x_461_ = l_Lean_Environment_header(v_env_434_);
lean_dec_ref(v_env_434_);
v___x_462_ = l_Lean_EnvironmentHeader_moduleNames(v___x_461_);
v_mod_463_ = lean_array_get(v___x_460_, v___x_462_, v_val_456_);
lean_dec(v_val_456_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_Lean_isPrivateName(v_declHint_430_);
lean_dec(v_declHint_430_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_c_447_);
v___x_467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_MessageData_ofName(v_mod_463_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_MessageData_note(v___x_472_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v_msg_429_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 0);
lean_ctor_set(v___x_458_, 0, v___x_474_);
v___x_476_ = v___x_458_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_478_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_c_447_);
v___x_480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_MessageData_ofName(v_mod_463_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_MessageData_note(v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v_msg_429_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 0);
lean_ctor_set(v___x_458_, 0, v___x_487_);
v___x_489_ = v___x_458_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_495_, lean_object* v_declHint_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_495_, v_declHint_496_, v___y_497_);
lean_dec(v___y_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(lean_object* v_msg_500_, lean_object* v_declHint_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v___x_505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_500_, v_declHint_501_, v___y_503_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = l_Lean_unknownIdentifierMessageTag;
v___x_511_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object* v_msg_516_, lean_object* v_declHint_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_516_, v_declHint_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v_env_527_; lean_object* v_options_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_526_ = lean_st_ref_get(v___y_524_);
v_env_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_env_527_);
lean_dec(v___x_526_);
v_options_528_ = lean_ctor_get(v___y_523_, 2);
v___x_529_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_530_ = lean_unsigned_to_nat(32u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
lean_dec_ref(v___x_531_);
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
lean_inc_ref(v_options_528_);
v___x_533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_533_, 0, v_env_527_);
lean_ctor_set(v___x_533_, 1, v___x_529_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_ctor_set(v___x_533_, 3, v_options_528_);
v___x_534_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_msgData_522_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msgData_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_ref_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_ref_545_ = lean_ctor_get(v___y_542_, 5);
v___x_546_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v_msg_541_, v___y_542_, v___y_543_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_ref_545_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_ref_545_);
lean_ctor_set(v___x_551_, 1, v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(lean_object* v_ref_561_, lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_fileName_566_; lean_object* v_fileMap_567_; lean_object* v_options_568_; lean_object* v_currRecDepth_569_; lean_object* v_maxRecDepth_570_; lean_object* v_ref_571_; lean_object* v_currNamespace_572_; lean_object* v_openDecls_573_; lean_object* v_initHeartbeats_574_; lean_object* v_maxHeartbeats_575_; lean_object* v_quotContext_576_; lean_object* v_currMacroScope_577_; uint8_t v_diag_578_; lean_object* v_cancelTk_x3f_579_; uint8_t v_suppressElabErrors_580_; lean_object* v_inheritedTraceOptions_581_; lean_object* v_ref_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_fileName_566_ = lean_ctor_get(v___y_563_, 0);
v_fileMap_567_ = lean_ctor_get(v___y_563_, 1);
v_options_568_ = lean_ctor_get(v___y_563_, 2);
v_currRecDepth_569_ = lean_ctor_get(v___y_563_, 3);
v_maxRecDepth_570_ = lean_ctor_get(v___y_563_, 4);
v_ref_571_ = lean_ctor_get(v___y_563_, 5);
v_currNamespace_572_ = lean_ctor_get(v___y_563_, 6);
v_openDecls_573_ = lean_ctor_get(v___y_563_, 7);
v_initHeartbeats_574_ = lean_ctor_get(v___y_563_, 8);
v_maxHeartbeats_575_ = lean_ctor_get(v___y_563_, 9);
v_quotContext_576_ = lean_ctor_get(v___y_563_, 10);
v_currMacroScope_577_ = lean_ctor_get(v___y_563_, 11);
v_diag_578_ = lean_ctor_get_uint8(v___y_563_, sizeof(void*)*14);
v_cancelTk_x3f_579_ = lean_ctor_get(v___y_563_, 12);
v_suppressElabErrors_580_ = lean_ctor_get_uint8(v___y_563_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_581_ = lean_ctor_get(v___y_563_, 13);
v_ref_582_ = l_Lean_replaceRef(v_ref_561_, v_ref_571_);
lean_inc_ref(v_inheritedTraceOptions_581_);
lean_inc(v_cancelTk_x3f_579_);
lean_inc(v_currMacroScope_577_);
lean_inc(v_quotContext_576_);
lean_inc(v_maxHeartbeats_575_);
lean_inc(v_initHeartbeats_574_);
lean_inc(v_openDecls_573_);
lean_inc(v_currNamespace_572_);
lean_inc(v_maxRecDepth_570_);
lean_inc(v_currRecDepth_569_);
lean_inc_ref(v_options_568_);
lean_inc_ref(v_fileMap_567_);
lean_inc_ref(v_fileName_566_);
v___x_583_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_583_, 0, v_fileName_566_);
lean_ctor_set(v___x_583_, 1, v_fileMap_567_);
lean_ctor_set(v___x_583_, 2, v_options_568_);
lean_ctor_set(v___x_583_, 3, v_currRecDepth_569_);
lean_ctor_set(v___x_583_, 4, v_maxRecDepth_570_);
lean_ctor_set(v___x_583_, 5, v_ref_582_);
lean_ctor_set(v___x_583_, 6, v_currNamespace_572_);
lean_ctor_set(v___x_583_, 7, v_openDecls_573_);
lean_ctor_set(v___x_583_, 8, v_initHeartbeats_574_);
lean_ctor_set(v___x_583_, 9, v_maxHeartbeats_575_);
lean_ctor_set(v___x_583_, 10, v_quotContext_576_);
lean_ctor_set(v___x_583_, 11, v_currMacroScope_577_);
lean_ctor_set(v___x_583_, 12, v_cancelTk_x3f_579_);
lean_ctor_set(v___x_583_, 13, v_inheritedTraceOptions_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*14, v_diag_578_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*14 + 1, v_suppressElabErrors_580_);
v___x_584_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_562_, v___x_583_, v___y_564_);
lean_dec_ref_known(v___x_583_, 14);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_ref_585_, lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_585_, v_msg_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v_ref_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_ref_591_, lean_object* v_msg_592_, lean_object* v_declHint_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v_a_598_; lean_object* v___x_599_; 
v___x_597_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_592_, v_declHint_593_, v___y_594_, v___y_595_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_597_);
v___x_599_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_591_, v_a_598_, v___y_594_, v___y_595_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_ref_600_, lean_object* v_msg_601_, lean_object* v_declHint_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_600_, v_msg_601_, v_declHint_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v_ref_600_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_ref_613_, lean_object* v_constName_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_618_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1);
v___x_619_ = 0;
lean_inc(v_constName_614_);
v___x_620_ = l_Lean_MessageData_ofConstName(v_constName_614_, v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_613_, v___x_623_, v_constName_614_, v___y_615_, v___y_616_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_ref_625_, lean_object* v_constName_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_625_, v_constName_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_ref_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_constName_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v___x_636_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 5);
v___x_636_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_635_, v_constName_631_, v___y_632_, v___y_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_constName_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(lean_object* v_constName_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_env_647_; uint8_t v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_647_);
lean_dec(v___x_646_);
v___x_648_ = 0;
lean_inc(v_constName_642_);
v___x_649_ = l_Lean_Environment_find_x3f(v_env_647_, v_constName_642_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_642_, v___y_643_, v___y_644_);
return v___x_650_;
}
else
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_constName_642_);
v_val_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_val_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3___boxed(lean_object* v_constName_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_constName_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t v___y_671_, uint8_t v_suppressElabErrors_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_673_) == 1)
{
lean_object* v_pre_674_; 
v_pre_674_ = lean_ctor_get(v_x_673_, 0);
switch(lean_obj_tag(v_pre_674_))
{
case 1:
{
lean_object* v_pre_675_; 
v_pre_675_ = lean_ctor_get(v_pre_674_, 0);
switch(lean_obj_tag(v_pre_675_))
{
case 0:
{
lean_object* v_str_676_; lean_object* v_str_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_str_676_ = lean_ctor_get(v_x_673_, 1);
v_str_677_ = lean_ctor_get(v_pre_674_, 1);
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_679_ = lean_string_dec_eq(v_str_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0));
v___x_681_ = lean_string_dec_eq(v_str_677_, v___x_680_);
if (v___x_681_ == 0)
{
return v___y_671_;
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1));
v___x_683_ = lean_string_dec_eq(v_str_676_, v___x_682_);
if (v___x_683_ == 0)
{
return v___y_671_;
}
else
{
return v_suppressElabErrors_672_;
}
}
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2));
v___x_685_ = lean_string_dec_eq(v_str_676_, v___x_684_);
if (v___x_685_ == 0)
{
return v___y_671_;
}
else
{
return v_suppressElabErrors_672_;
}
}
}
case 1:
{
lean_object* v_pre_686_; 
v_pre_686_ = lean_ctor_get(v_pre_675_, 0);
if (lean_obj_tag(v_pre_686_) == 0)
{
lean_object* v_str_687_; lean_object* v_str_688_; lean_object* v_str_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_str_687_ = lean_ctor_get(v_x_673_, 1);
v_str_688_ = lean_ctor_get(v_pre_674_, 1);
v_str_689_ = lean_ctor_get(v_pre_675_, 1);
v___x_690_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3));
v___x_691_ = lean_string_dec_eq(v_str_689_, v___x_690_);
if (v___x_691_ == 0)
{
return v___y_671_;
}
else
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4));
v___x_693_ = lean_string_dec_eq(v_str_688_, v___x_692_);
if (v___x_693_ == 0)
{
return v___y_671_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5));
v___x_695_ = lean_string_dec_eq(v_str_687_, v___x_694_);
if (v___x_695_ == 0)
{
return v___y_671_;
}
else
{
return v_suppressElabErrors_672_;
}
}
}
}
else
{
return v___y_671_;
}
}
default: 
{
return v___y_671_;
}
}
}
case 0:
{
lean_object* v_str_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_str_696_ = lean_ctor_get(v_x_673_, 1);
v___x_697_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6));
v___x_698_ = lean_string_dec_eq(v_str_696_, v___x_697_);
if (v___x_698_ == 0)
{
return v___y_671_;
}
else
{
return v_suppressElabErrors_672_;
}
}
default: 
{
return v___y_671_;
}
}
}
else
{
return v___y_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___y_699_, lean_object* v_suppressElabErrors_700_, lean_object* v_x_701_){
_start:
{
uint8_t v___y_10689__boxed_702_; uint8_t v_suppressElabErrors_boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v___y_10689__boxed_702_ = lean_unbox(v___y_699_);
v_suppressElabErrors_boxed_703_ = lean_unbox(v_suppressElabErrors_700_);
v_res_704_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_10689__boxed_702_, v_suppressElabErrors_boxed_703_, v_x_701_);
lean_dec(v_x_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_opts_706_, lean_object* v_opt_707_){
_start:
{
lean_object* v_name_708_; lean_object* v_defValue_709_; lean_object* v_map_710_; lean_object* v___x_711_; 
v_name_708_ = lean_ctor_get(v_opt_707_, 0);
v_defValue_709_ = lean_ctor_get(v_opt_707_, 1);
v_map_710_ = lean_ctor_get(v_opts_706_, 0);
v___x_711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_710_, v_name_708_);
if (lean_obj_tag(v___x_711_) == 0)
{
uint8_t v___x_712_; 
v___x_712_ = lean_unbox(v_defValue_709_);
return v___x_712_;
}
else
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_711_, 1);
if (lean_obj_tag(v_val_713_) == 1)
{
uint8_t v_v_714_; 
v_v_714_ = lean_ctor_get_uint8(v_val_713_, 0);
lean_dec_ref_known(v_val_713_, 0);
return v_v_714_;
}
else
{
uint8_t v___x_715_; 
lean_dec(v_val_713_);
v___x_715_ = lean_unbox(v_defValue_709_);
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_716_, lean_object* v_opt_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_opts_716_, v_opt_717_);
lean_dec_ref(v_opt_717_);
lean_dec_ref(v_opts_716_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_ref_721_, lean_object* v_msgData_722_, uint8_t v_severity_723_, uint8_t v_isSilent_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_765_; lean_object* v___y_766_; uint8_t v___y_767_; uint8_t v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v___y_772_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; uint8_t v___y_807_; uint8_t v___x_812_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; uint8_t v___y_818_; uint8_t v___y_819_; uint8_t v___y_820_; uint8_t v___y_822_; uint8_t v___x_837_; 
v___x_812_ = 2;
v___x_837_ = l_Lean_instBEqMessageSeverity_beq(v_severity_723_, v___x_812_);
if (v___x_837_ == 0)
{
v___y_822_ = v___x_837_;
goto v___jp_821_;
}
else
{
uint8_t v___x_838_; 
lean_inc_ref(v_msgData_722_);
v___x_838_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_722_);
v___y_822_ = v___x_838_;
goto v___jp_821_;
}
v___jp_728_:
{
lean_object* v___x_738_; lean_object* v_currNamespace_739_; lean_object* v_openDecls_740_; lean_object* v_env_741_; lean_object* v_nextMacroScope_742_; lean_object* v_ngen_743_; lean_object* v_auxDeclNGen_744_; lean_object* v_traceState_745_; lean_object* v_cache_746_; lean_object* v_messages_747_; lean_object* v_infoState_748_; lean_object* v_snapshotTasks_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_763_; 
v___x_738_ = lean_st_ref_take(v___y_737_);
v_currNamespace_739_ = lean_ctor_get(v___y_736_, 6);
v_openDecls_740_ = lean_ctor_get(v___y_736_, 7);
v_env_741_ = lean_ctor_get(v___x_738_, 0);
v_nextMacroScope_742_ = lean_ctor_get(v___x_738_, 1);
v_ngen_743_ = lean_ctor_get(v___x_738_, 2);
v_auxDeclNGen_744_ = lean_ctor_get(v___x_738_, 3);
v_traceState_745_ = lean_ctor_get(v___x_738_, 4);
v_cache_746_ = lean_ctor_get(v___x_738_, 5);
v_messages_747_ = lean_ctor_get(v___x_738_, 6);
v_infoState_748_ = lean_ctor_get(v___x_738_, 7);
v_snapshotTasks_749_ = lean_ctor_get(v___x_738_, 8);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_763_ == 0)
{
v___x_751_ = v___x_738_;
v_isShared_752_ = v_isSharedCheck_763_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snapshotTasks_749_);
lean_inc(v_infoState_748_);
lean_inc(v_messages_747_);
lean_inc(v_cache_746_);
lean_inc(v_traceState_745_);
lean_inc(v_auxDeclNGen_744_);
lean_inc(v_ngen_743_);
lean_inc(v_nextMacroScope_742_);
lean_inc(v_env_741_);
lean_dec(v___x_738_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_763_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_openDecls_740_);
lean_inc(v_currNamespace_739_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_currNamespace_739_);
lean_ctor_set(v___x_753_, 1, v_openDecls_740_);
v___x_754_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___y_733_);
lean_inc_ref(v___y_734_);
lean_inc_ref(v___y_735_);
v___x_755_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_755_, 0, v___y_735_);
lean_ctor_set(v___x_755_, 1, v___y_730_);
lean_ctor_set(v___x_755_, 2, v___y_729_);
lean_ctor_set(v___x_755_, 3, v___y_734_);
lean_ctor_set(v___x_755_, 4, v___x_754_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*5, v___y_732_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*5 + 1, v___y_731_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*5 + 2, v_isSilent_724_);
v___x_756_ = l_Lean_MessageLog_add(v___x_755_, v_messages_747_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 6, v___x_756_);
v___x_758_ = v___x_751_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_env_741_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_nextMacroScope_742_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_ngen_743_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_auxDeclNGen_744_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_traceState_745_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v_cache_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_762_, 7, v_infoState_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 8, v_snapshotTasks_749_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_st_ref_set(v___y_737_, v___x_758_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
v___jp_764_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_788_; 
v___x_773_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_722_);
v___x_774_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0_spec__0(v___x_773_, v___y_725_, v___y_726_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref_n(v___y_766_, 2);
v___x_779_ = l_Lean_FileMap_toPosition(v___y_766_, v___y_770_);
lean_dec(v___y_770_);
v___x_780_ = l_Lean_FileMap_toPosition(v___y_766_, v___y_772_);
lean_dec(v___y_772_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_771_ == 0)
{
lean_del_object(v___x_777_);
lean_dec_ref(v___y_765_);
v___y_729_ = v___x_781_;
v___y_730_ = v___x_779_;
v___y_731_ = v___y_767_;
v___y_732_ = v___y_768_;
v___y_733_ = v_a_775_;
v___y_734_ = v___x_782_;
v___y_735_ = v___y_769_;
v___y_736_ = v___y_725_;
v___y_737_ = v___y_726_;
goto v___jp_728_;
}
else
{
uint8_t v___x_783_; 
lean_inc(v_a_775_);
v___x_783_ = l_Lean_MessageData_hasTag(v___y_765_, v_a_775_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_781_, 1);
lean_dec_ref(v___x_779_);
lean_dec(v_a_775_);
v___x_784_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_784_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_del_object(v___x_777_);
v___y_729_ = v___x_781_;
v___y_730_ = v___x_779_;
v___y_731_ = v___y_767_;
v___y_732_ = v___y_768_;
v___y_733_ = v_a_775_;
v___y_734_ = v___x_782_;
v___y_735_ = v___y_769_;
v___y_736_ = v___y_725_;
v___y_737_ = v___y_726_;
goto v___jp_728_;
}
}
}
}
v___jp_789_:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Syntax_getTailPos_x3f(v___y_791_, v___y_794_);
lean_dec(v___y_791_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_inc(v___y_797_);
v___y_765_ = v___y_790_;
v___y_766_ = v___y_792_;
v___y_767_ = v___y_793_;
v___y_768_ = v___y_794_;
v___y_769_ = v___y_795_;
v___y_770_ = v___y_797_;
v___y_771_ = v___y_796_;
v___y_772_ = v___y_797_;
goto v___jp_764_;
}
else
{
lean_object* v_val_799_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
v___y_765_ = v___y_790_;
v___y_766_ = v___y_792_;
v___y_767_ = v___y_793_;
v___y_768_ = v___y_794_;
v___y_769_ = v___y_795_;
v___y_770_ = v___y_797_;
v___y_771_ = v___y_796_;
v___y_772_ = v_val_799_;
goto v___jp_764_;
}
}
v___jp_800_:
{
lean_object* v_ref_808_; lean_object* v___x_809_; 
v_ref_808_ = l_Lean_replaceRef(v_ref_721_, v___y_805_);
v___x_809_ = l_Lean_Syntax_getPos_x3f(v_ref_808_, v___y_803_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___y_790_ = v___y_801_;
v___y_791_ = v_ref_808_;
v___y_792_ = v___y_802_;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_803_;
v___y_795_ = v___y_804_;
v___y_796_ = v___y_806_;
v___y_797_ = v___x_810_;
goto v___jp_789_;
}
else
{
lean_object* v_val_811_; 
v_val_811_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_809_, 1);
v___y_790_ = v___y_801_;
v___y_791_ = v_ref_808_;
v___y_792_ = v___y_802_;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_803_;
v___y_795_ = v___y_804_;
v___y_796_ = v___y_806_;
v___y_797_ = v_val_811_;
goto v___jp_789_;
}
}
v___jp_813_:
{
if (v___y_820_ == 0)
{
v___y_801_ = v___y_815_;
v___y_802_ = v___y_814_;
v___y_803_ = v___y_819_;
v___y_804_ = v___y_816_;
v___y_805_ = v___y_817_;
v___y_806_ = v___y_818_;
v___y_807_ = v_severity_723_;
goto v___jp_800_;
}
else
{
v___y_801_ = v___y_815_;
v___y_802_ = v___y_814_;
v___y_803_ = v___y_819_;
v___y_804_ = v___y_816_;
v___y_805_ = v___y_817_;
v___y_806_ = v___y_818_;
v___y_807_ = v___x_812_;
goto v___jp_800_;
}
}
v___jp_821_:
{
if (v___y_822_ == 0)
{
lean_object* v_fileName_823_; lean_object* v_fileMap_824_; lean_object* v_options_825_; lean_object* v_ref_826_; uint8_t v_suppressElabErrors_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___f_830_; uint8_t v___x_831_; uint8_t v___x_832_; 
v_fileName_823_ = lean_ctor_get(v___y_725_, 0);
v_fileMap_824_ = lean_ctor_get(v___y_725_, 1);
v_options_825_ = lean_ctor_get(v___y_725_, 2);
v_ref_826_ = lean_ctor_get(v___y_725_, 5);
v_suppressElabErrors_827_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*14 + 1);
v___x_828_ = lean_box(v___y_822_);
v___x_829_ = lean_box(v_suppressElabErrors_827_);
v___f_830_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_830_, 0, v___x_828_);
lean_closure_set(v___f_830_, 1, v___x_829_);
v___x_831_ = 1;
v___x_832_ = l_Lean_instBEqMessageSeverity_beq(v_severity_723_, v___x_831_);
if (v___x_832_ == 0)
{
v___y_814_ = v_fileMap_824_;
v___y_815_ = v___f_830_;
v___y_816_ = v_fileName_823_;
v___y_817_ = v_ref_826_;
v___y_818_ = v_suppressElabErrors_827_;
v___y_819_ = v___y_822_;
v___y_820_ = v___x_832_;
goto v___jp_813_;
}
else
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = l_Lean_warningAsError;
v___x_834_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_825_, v___x_833_);
v___y_814_ = v_fileMap_824_;
v___y_815_ = v___f_830_;
v___y_816_ = v_fileName_823_;
v___y_817_ = v_ref_826_;
v___y_818_ = v_suppressElabErrors_827_;
v___y_819_ = v___y_822_;
v___y_820_ = v___x_834_;
goto v___jp_813_;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_msgData_722_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_ref_839_, lean_object* v_msgData_840_, lean_object* v_severity_841_, lean_object* v_isSilent_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
uint8_t v_severity_boxed_846_; uint8_t v_isSilent_boxed_847_; lean_object* v_res_848_; 
v_severity_boxed_846_ = lean_unbox(v_severity_841_);
v_isSilent_boxed_847_ = lean_unbox(v_isSilent_842_);
v_res_848_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_839_, v_msgData_840_, v_severity_boxed_846_, v_isSilent_boxed_847_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v_ref_839_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_849_, uint8_t v_severity_850_, uint8_t v_isSilent_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_ref_855_; lean_object* v___x_856_; 
v_ref_855_ = lean_ctor_get(v___y_852_, 5);
v___x_856_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_855_, v_msgData_849_, v_severity_850_, v_isSilent_851_, v___y_852_, v___y_853_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_857_, lean_object* v_severity_858_, lean_object* v_isSilent_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v_severity_boxed_863_; uint8_t v_isSilent_boxed_864_; lean_object* v_res_865_; 
v_severity_boxed_863_ = lean_unbox(v_severity_858_);
v_isSilent_boxed_864_ = lean_unbox(v_isSilent_859_);
v_res_865_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_857_, v_severity_boxed_863_, v_isSilent_boxed_864_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(lean_object* v_msgData_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; 
v___x_870_ = 1;
v___x_871_ = 0;
v___x_872_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__2(v_msgData_866_, v___x_870_, v___x_871_, v___y_867_, v___y_868_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v_msgData_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_887_ = l_Lean_MessageData_ofFormat(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_907_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_ctor_set(v___x_907_, 3, v___x_906_);
lean_ctor_set(v___x_907_, 4, v___x_906_);
lean_ctor_set(v___x_907_, 5, v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
lean_ctor_set(v___x_909_, 3, v___x_908_);
lean_ctor_set(v___x_909_, 4, v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___f_917_, lean_object* v___x_918_, lean_object* v_declName_919_, lean_object* v_stx_920_, uint8_t v___kind_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v_a_1021_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; 
v___x_957_ = l_Lean_Name_mkStr2(v___x_913_, v___x_914_);
lean_inc(v_stx_920_);
v___x_958_ = l_Lean_Syntax_isOfKind(v_stx_920_, v___x_957_);
lean_dec(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_stx_920_);
lean_dec(v_declName_919_);
lean_dec_ref(v___f_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___x_1134_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1135_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1134_, v___y_922_, v___y_923_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v_oldId_1137_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v_since_x3f_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_text_x3f_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v_newId_x3f_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
v_oldId_1137_ = l_Lean_Syntax_getArg(v_stx_920_, v___x_1136_);
v___x_1184_ = l_Lean_Syntax_getArg(v_stx_920_, v___x_918_);
v___x_1185_ = l_Lean_Syntax_isNone(v___x_1184_);
if (v___x_1185_ == 0)
{
uint8_t v___x_1186_; 
lean_inc(v___x_1184_);
v___x_1186_ = l_Lean_Syntax_matchesNull(v___x_1184_, v___x_1136_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v___x_1184_);
lean_dec(v_oldId_1137_);
lean_dec(v_stx_920_);
lean_dec(v_declName_919_);
lean_dec_ref(v___f_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___x_1187_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1188_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1187_, v___y_922_, v___y_923_);
return v___x_1188_;
}
else
{
lean_object* v_newId_x3f_1189_; lean_object* v___x_1190_; 
v_newId_x3f_1189_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_916_);
lean_dec(v___x_1184_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_newId_x3f_1189_);
v_newId_x3f_1172_ = v___x_1190_;
v___y_1173_ = v___y_922_;
v___y_1174_ = v___y_923_;
goto v___jp_1171_;
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___x_1184_);
v___x_1191_ = lean_box(0);
v_newId_x3f_1172_ = v___x_1191_;
v___y_1173_ = v___y_922_;
v___y_1174_ = v___y_923_;
goto v___jp_1171_;
}
v___jp_1138_:
{
lean_object* v_oldArg_1144_; 
v_oldArg_1144_ = l_Lean_TSyntax_getId(v_oldId_1137_);
lean_dec(v_oldId_1137_);
if (lean_obj_tag(v___y_1139_) == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_box(0);
v___y_1114_ = v___y_1140_;
v___y_1115_ = v___y_1143_;
v___y_1116_ = v_oldArg_1144_;
v___y_1117_ = v_since_x3f_1141_;
v___y_1118_ = v___y_1142_;
v___y_1119_ = v___x_1145_;
goto v___jp_1113_;
}
else
{
lean_object* v_val_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_val_1146_ = lean_ctor_get(v___y_1139_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___y_1139_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___y_1139_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_val_1146_);
lean_dec(v___y_1139_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_TSyntax_getId(v_val_1146_);
lean_dec(v_val_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v___y_1114_ = v___y_1140_;
v___y_1115_ = v___y_1143_;
v___y_1116_ = v_oldArg_1144_;
v___y_1117_ = v_since_x3f_1141_;
v___y_1118_ = v___y_1142_;
v___y_1119_ = v___x_1152_;
goto v___jp_1113_;
}
}
}
}
v___jp_1155_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(4u);
v___x_1162_ = l_Lean_Syntax_getArg(v_stx_920_, v___x_1161_);
lean_dec(v_stx_920_);
v___x_1163_ = l_Lean_Syntax_isNone(v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1162_);
v___x_1165_ = l_Lean_Syntax_matchesNull(v___x_1162_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v___x_1162_);
lean_dec(v_text_x3f_1158_);
lean_dec(v___y_1156_);
lean_dec(v_oldId_1137_);
lean_dec(v_declName_919_);
lean_dec_ref(v___f_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___x_1166_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1167_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1166_, v___y_1159_, v___y_1160_);
return v___x_1167_;
}
else
{
lean_object* v_since_x3f_1168_; lean_object* v___x_1169_; 
v_since_x3f_1168_ = l_Lean_Syntax_getArg(v___x_1162_, v___y_1157_);
lean_dec(v___x_1162_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_since_x3f_1168_);
v___y_1139_ = v___y_1156_;
v___y_1140_ = v_text_x3f_1158_;
v_since_x3f_1141_ = v___x_1169_;
v___y_1142_ = v___y_1159_;
v___y_1143_ = v___y_1160_;
goto v___jp_1138_;
}
}
else
{
lean_object* v___x_1170_; 
lean_dec(v___x_1162_);
v___x_1170_ = lean_box(0);
v___y_1139_ = v___y_1156_;
v___y_1140_ = v_text_x3f_1158_;
v_since_x3f_1141_ = v___x_1170_;
v___y_1142_ = v___y_1159_;
v___y_1143_ = v___y_1160_;
goto v___jp_1138_;
}
}
v___jp_1171_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(3u);
v___x_1176_ = l_Lean_Syntax_getArg(v_stx_920_, v___x_1175_);
v___x_1177_ = l_Lean_Syntax_isNone(v___x_1176_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; 
lean_inc(v___x_1176_);
v___x_1178_ = l_Lean_Syntax_matchesNull(v___x_1176_, v___x_1136_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v___x_1176_);
lean_dec(v_newId_x3f_1172_);
lean_dec(v_oldId_1137_);
lean_dec(v_stx_920_);
lean_dec(v_declName_919_);
lean_dec_ref(v___f_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___x_1179_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1180_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1179_, v___y_1173_, v___y_1174_);
return v___x_1180_;
}
else
{
lean_object* v_text_x3f_1181_; lean_object* v___x_1182_; 
v_text_x3f_1181_ = l_Lean_Syntax_getArg(v___x_1176_, v___x_916_);
lean_dec(v___x_1176_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_text_x3f_1181_);
v___y_1156_ = v_newId_x3f_1172_;
v___y_1157_ = v___x_1175_;
v_text_x3f_1158_ = v___x_1182_;
v___y_1159_ = v___y_1173_;
v___y_1160_ = v___y_1174_;
goto v___jp_1155_;
}
}
else
{
lean_object* v___x_1183_; 
lean_dec(v___x_1176_);
v___x_1183_ = lean_box(0);
v___y_1156_ = v_newId_x3f_1172_;
v___y_1157_ = v___x_1175_;
v_text_x3f_1158_ = v___x_1183_;
v___y_1159_ = v___y_1173_;
v___y_1160_ = v___y_1174_;
goto v___jp_1155_;
}
}
}
v___jp_925_:
{
lean_object* v___x_931_; lean_object* v_env_932_; lean_object* v_nextMacroScope_933_; lean_object* v_ngen_934_; lean_object* v_auxDeclNGen_935_; lean_object* v_traceState_936_; lean_object* v_messages_937_; lean_object* v_infoState_938_; lean_object* v_snapshotTasks_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_955_; 
v___x_931_ = lean_st_ref_take(v___y_930_);
v_env_932_ = lean_ctor_get(v___x_931_, 0);
v_nextMacroScope_933_ = lean_ctor_get(v___x_931_, 1);
v_ngen_934_ = lean_ctor_get(v___x_931_, 2);
v_auxDeclNGen_935_ = lean_ctor_get(v___x_931_, 3);
v_traceState_936_ = lean_ctor_get(v___x_931_, 4);
v_messages_937_ = lean_ctor_get(v___x_931_, 6);
v_infoState_938_ = lean_ctor_get(v___x_931_, 7);
v_snapshotTasks_939_ = lean_ctor_get(v___x_931_, 8);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_931_, 5);
lean_dec(v_unused_956_);
v___x_941_ = v___x_931_;
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snapshotTasks_939_);
lean_inc(v_infoState_938_);
lean_inc(v_messages_937_);
lean_inc(v_traceState_936_);
lean_inc(v_auxDeclNGen_935_);
lean_inc(v_ngen_934_);
lean_inc(v_nextMacroScope_933_);
lean_inc(v_env_932_);
lean_dec(v___x_931_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_toEnvExtension_944_; lean_object* v_asyncMode_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_943_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_944_ = lean_ctor_get(v___x_943_, 0);
v_asyncMode_945_ = lean_ctor_get(v_toEnvExtension_944_, 2);
v___x_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_946_, 0, v_declName_919_);
lean_ctor_set(v___x_946_, 1, v___y_929_);
lean_ctor_set(v___x_946_, 2, v___y_928_);
lean_ctor_set(v___x_946_, 3, v___y_927_);
lean_ctor_set(v___x_946_, 4, v___y_926_);
v___x_947_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_943_, v_env_932_, v___x_946_, v_asyncMode_945_, v___x_915_);
v___x_948_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 5, v___x_948_);
lean_ctor_set(v___x_941_, 0, v___x_947_);
v___x_950_ = v___x_941_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_nextMacroScope_933_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_ngen_934_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_auxDeclNGen_935_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_traceState_936_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_954_, 6, v_messages_937_);
lean_ctor_set(v_reuseFailAlloc_954_, 7, v_infoState_938_);
lean_ctor_set(v_reuseFailAlloc_954_, 8, v_snapshotTasks_939_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_st_ref_set(v___y_930_, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
v___jp_959_:
{
if (lean_obj_tag(v___y_960_) == 0)
{
if (v___x_958_ == 0)
{
v___y_926_ = v___y_960_;
v___y_927_ = v___y_961_;
v___y_928_ = v___y_962_;
v___y_929_ = v___y_963_;
v___y_930_ = v___y_965_;
goto v___jp_925_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_967_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v___x_966_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref_known(v___x_967_, 1);
v___y_926_ = v___y_960_;
v___y_927_ = v___y_961_;
v___y_928_ = v___y_962_;
v___y_929_ = v___y_963_;
v___y_930_ = v___y_965_;
goto v___jp_925_;
}
else
{
lean_dec(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v_declName_919_);
lean_dec(v___x_915_);
return v___x_967_;
}
}
}
else
{
v___y_926_ = v___y_960_;
v___y_927_ = v___y_961_;
v___y_928_ = v___y_962_;
v___y_929_ = v___y_963_;
v___y_930_ = v___y_965_;
goto v___jp_925_;
}
}
v___jp_968_:
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_array_get_size(v___y_972_);
v___x_978_ = lean_nat_dec_lt(v___x_916_, v___x_977_);
lean_dec(v___x_916_);
if (v___x_978_ == 0)
{
lean_dec_ref(v___y_972_);
lean_dec(v___y_970_);
v___y_960_ = v___y_969_;
v___y_961_ = v___y_971_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
v___y_964_ = v___y_975_;
v___y_965_ = v___y_976_;
goto v___jp_959_;
}
else
{
if (v___x_978_ == 0)
{
lean_dec_ref(v___y_972_);
lean_dec(v___y_970_);
v___y_960_ = v___y_969_;
v___y_961_ = v___y_971_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
v___y_964_ = v___y_975_;
v___y_965_ = v___y_976_;
goto v___jp_959_;
}
else
{
size_t v___x_979_; size_t v___x_980_; uint8_t v___x_981_; 
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_977_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v___y_974_, v___y_972_, v___x_979_, v___x_980_);
lean_dec_ref(v___y_972_);
if (v___x_981_ == 0)
{
lean_dec(v___y_970_);
v___y_960_ = v___y_969_;
v___y_961_ = v___y_971_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
v___y_964_ = v___y_975_;
v___y_965_ = v___y_976_;
goto v___jp_959_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v___y_973_);
lean_dec(v___y_971_);
lean_dec(v___y_969_);
lean_dec(v___x_915_);
v___x_982_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_983_ = l_Lean_MessageData_ofName(v___y_974_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_MessageData_ofName(v_declName_919_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_MessageData_ofName(v___y_970_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_994_, v___y_975_, v___y_976_);
return v___x_995_;
}
}
}
}
v___jp_996_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_997_);
v___x_1005_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1006_ = l_Lean_MessageData_ofName(v___y_999_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_MessageData_ofName(v_declName_919_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1005_);
v___x_1013_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1012_, v___y_1004_, v___y_998_);
return v___x_1013_;
}
v___jp_1014_:
{
if (lean_obj_tag(v___y_1018_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_val_1022_ = lean_ctor_get(v___y_1018_, 0);
lean_inc(v_val_1022_);
v___x_1023_ = lean_array_get_size(v_a_1021_);
v___x_1024_ = lean_nat_dec_lt(v___x_916_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1022_;
v___y_1000_ = v_a_1021_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
v___y_1003_ = v___y_1019_;
v___y_1004_ = v___y_1020_;
goto v___jp_996_;
}
else
{
if (v___x_1024_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1022_;
v___y_1000_ = v_a_1021_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
v___y_1003_ = v___y_1019_;
v___y_1004_ = v___y_1020_;
goto v___jp_996_;
}
else
{
size_t v___x_1025_; size_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1023_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_val_1022_, v_a_1021_, v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1022_;
v___y_1000_ = v_a_1021_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
v___y_1003_ = v___y_1019_;
v___y_1004_ = v___y_1020_;
goto v___jp_996_;
}
else
{
v___y_969_ = v___y_1015_;
v___y_970_ = v_val_1022_;
v___y_971_ = v___y_1017_;
v___y_972_ = v_a_1021_;
v___y_973_ = v___y_1018_;
v___y_974_ = v___y_1019_;
v___y_975_ = v___y_1020_;
v___y_976_ = v___y_1016_;
goto v___jp_968_;
}
}
}
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_a_1021_);
v___x_1029_ = lean_nat_dec_lt(v___x_916_, v___x_1028_);
lean_dec(v___x_916_);
if (v___x_1029_ == 0)
{
lean_dec_ref(v_a_1021_);
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1018_;
v___y_963_ = v___y_1019_;
v___y_964_ = v___y_1020_;
v___y_965_ = v___y_1016_;
goto v___jp_959_;
}
else
{
if (v___x_1029_ == 0)
{
lean_dec_ref(v_a_1021_);
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1018_;
v___y_963_ = v___y_1019_;
v___y_964_ = v___y_1020_;
v___y_965_ = v___y_1016_;
goto v___jp_959_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = lean_usize_of_nat(v___x_1028_);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v___y_1019_, v_a_1021_, v___x_1030_, v___x_1031_);
lean_dec_ref(v_a_1021_);
if (v___x_1032_ == 0)
{
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1018_;
v___y_963_ = v___y_1019_;
v___y_964_ = v___y_1020_;
v___y_965_ = v___y_1016_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec(v___y_1015_);
lean_dec(v___x_915_);
v___x_1033_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1034_ = l_Lean_MessageData_ofName(v___y_1019_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_ofName(v_declName_919_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1041_, v___y_1020_, v___y_1016_);
return v___x_1042_;
}
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1050_; 
lean_inc(v_declName_919_);
v___x_1050_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_declName_919_, v___y_1048_, v___y_1044_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; uint64_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = 0;
v___x_1053_ = 1;
v___x_1054_ = 0;
v___x_1055_ = 2;
v___x_1056_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1056_, 0, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 1, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 2, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 3, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 4, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 5, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 6, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 7, v___x_1052_);
lean_ctor_set_uint8(v___x_1056_, 8, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 9, v___x_1053_);
lean_ctor_set_uint8(v___x_1056_, 10, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, 11, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 12, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 13, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 14, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, 15, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 16, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 17, v___x_958_);
lean_ctor_set_uint8(v___x_1056_, 18, v___x_958_);
v___x_1057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set_uint64(v___x_1058_, sizeof(void*)*1, v___x_1057_);
v___x_1059_ = lean_box(1);
v___x_1060_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1061_ = lean_unsigned_to_nat(32u);
v___x_1062_ = lean_mk_empty_array_with_capacity(v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_1064_ = ((size_t)5ULL);
lean_inc_n(v___x_916_, 7);
v___x_1065_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1062_);
lean_ctor_set(v___x_1065_, 2, v___x_916_);
lean_ctor_set(v___x_1065_, 3, v___x_916_);
lean_ctor_set_usize(v___x_1065_, 4, v___x_1064_);
lean_inc_ref(v___x_1065_);
v___x_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1060_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_ctor_set(v___x_1066_, 2, v___x_1059_);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_916_);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1069_, 0, v___x_1058_);
lean_ctor_set(v___x_1069_, 1, v___x_1059_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
lean_ctor_set(v___x_1069_, 3, v___x_1067_);
lean_ctor_set(v___x_1069_, 4, v___x_1068_);
lean_ctor_set(v___x_1069_, 5, v___x_916_);
lean_ctor_set(v___x_1069_, 6, v___x_1068_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*7, v___x_1052_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*7 + 1, v___x_1052_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*7 + 2, v___x_1052_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*7 + 3, v___x_958_);
v___x_1070_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1070_, 0, v___x_916_);
lean_ctor_set(v___x_1070_, 1, v___x_916_);
lean_ctor_set(v___x_1070_, 2, v___x_916_);
lean_ctor_set(v___x_1070_, 3, v___x_916_);
lean_ctor_set(v___x_1070_, 4, v___x_1060_);
lean_ctor_set(v___x_1070_, 5, v___x_1060_);
lean_ctor_set(v___x_1070_, 6, v___x_1060_);
lean_ctor_set(v___x_1070_, 7, v___x_1060_);
lean_ctor_set(v___x_1070_, 8, v___x_1060_);
lean_ctor_set(v___x_1070_, 9, v___x_1060_);
v___x_1071_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1072_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_ctor_set(v___x_1073_, 2, v___x_1059_);
lean_ctor_set(v___x_1073_, 3, v___x_1065_);
lean_ctor_set(v___x_1073_, 4, v___x_1072_);
v___x_1074_ = lean_st_mk_ref(v___x_1073_);
v___x_1075_ = l_Lean_ConstantInfo_type(v_a_1051_);
lean_dec(v_a_1051_);
v___x_1076_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v___x_1075_, v___f_917_, v___x_1052_, v___x_1052_, v___x_1069_, v___x_1074_, v___y_1048_, v___y_1044_);
lean_dec_ref_known(v___x_1069_, 7);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = lean_st_ref_get(v___x_1074_);
lean_dec(v___x_1074_);
lean_dec(v___x_1078_);
v___y_1015_ = v___y_1049_;
v___y_1016_ = v___y_1044_;
v___y_1017_ = v___y_1045_;
v___y_1018_ = v___y_1046_;
v___y_1019_ = v___y_1047_;
v___y_1020_ = v___y_1048_;
v_a_1021_ = v_a_1077_;
goto v___jp_1014_;
}
else
{
lean_dec(v___x_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1076_, 1);
v___y_1015_ = v___y_1049_;
v___y_1016_ = v___y_1044_;
v___y_1017_ = v___y_1045_;
v___y_1018_ = v___y_1046_;
v___y_1019_ = v___y_1047_;
v___y_1020_ = v___y_1048_;
v_a_1021_ = v_a_1079_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v_declName_919_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v_a_1080_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1076_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1076_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v_declName_919_);
lean_dec_ref(v___f_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
v_a_1088_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1050_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1050_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
v___jp_1096_:
{
if (lean_obj_tag(v___y_1100_) == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_box(0);
v___y_1044_ = v___y_1097_;
v___y_1045_ = v___y_1102_;
v___y_1046_ = v___y_1098_;
v___y_1047_ = v___y_1099_;
v___y_1048_ = v___y_1101_;
v___y_1049_ = v___x_1103_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v_val_1104_ = lean_ctor_get(v___y_1100_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___y_1100_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1106_ = v___y_1100_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_val_1104_);
lean_dec(v___y_1100_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_TSyntax_getString(v_val_1104_);
lean_dec(v_val_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v___y_1044_ = v___y_1097_;
v___y_1045_ = v___y_1102_;
v___y_1046_ = v___y_1098_;
v___y_1047_ = v___y_1099_;
v___y_1048_ = v___y_1101_;
v___y_1049_ = v___x_1110_;
goto v___jp_1043_;
}
}
}
}
v___jp_1113_:
{
if (lean_obj_tag(v___y_1114_) == 0)
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_box(0);
v___y_1097_ = v___y_1115_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v___y_1101_ = v___y_1118_;
v___y_1102_ = v___x_1120_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1133_; 
v_val_1121_ = lean_ctor_get(v___y_1114_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___y_1114_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1123_ = v___y_1114_;
v_isShared_1124_ = v_isSharedCheck_1133_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v___y_1114_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1133_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = l_Lean_TSyntax_getString(v_val_1121_);
lean_dec(v_val_1121_);
v___x_1126_ = lean_string_utf8_byte_size(v___x_1125_);
v___x_1127_ = lean_nat_dec_eq(v___x_1126_, v___x_916_);
v___x_1128_ = lean_bool_not(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1125_);
lean_del_object(v___x_1123_);
v___x_1129_ = lean_box(0);
v___y_1097_ = v___y_1115_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v___y_1101_ = v___y_1118_;
v___y_1102_ = v___x_1129_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1131_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1131_ = v___x_1123_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1125_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1097_ = v___y_1115_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v___y_1101_ = v___y_1118_;
v___y_1102_ = v___x_1131_;
goto v___jp_1096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___f_1196_, lean_object* v___x_1197_, lean_object* v_declName_1198_, lean_object* v_stx_1199_, lean_object* v___kind_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v___kind_boxed_1204_; lean_object* v_res_1205_; 
v___kind_boxed_1204_ = lean_unbox(v___kind_1200_);
v_res_1205_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_1192_, v___x_1193_, v___x_1194_, v___x_1195_, v___f_1196_, v___x_1197_, v_declName_1198_, v_stx_1199_, v___kind_boxed_1204_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___x_1197_);
return v_res_1205_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v___x_1212_, lean_object* v_decl_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1217_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1218_ = l_Lean_MessageData_ofName(v___x_1212_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v___x_1221_, v___y_1214_, v___y_1215_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v___x_1223_, lean_object* v_decl_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_1223_, v_decl_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_decl_1224_);
return v_res_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(3249530483u);
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1272_ = l_Lean_Name_num___override(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1276_ = l_Lean_Name_str___override(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1279_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1280_ = l_Lean_Name_str___override(v___x_1279_, v___x_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_unsigned_to_nat(2u);
v___x_1282_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1283_ = l_Lean_Name_num___override(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1297_ = 0;
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1300_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1301_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
lean_ctor_set(v___x_1301_, 2, v___x_1298_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*3, v___x_1297_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___f_1302_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___f_1303_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1304_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___f_1303_);
lean_ctor_set(v___x_1305_, 2, v___f_1302_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1308_ = l_Lean_registerBuiltinAttribute(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_msg_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(v_00_u03b1_1317_, v_msg_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_bs_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___redArg(v_sz_1323_, v_i_1324_, v_bs_1325_, v___y_1326_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_bs_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
size_t v_sz_boxed_1340_; size_t v_i_boxed_1341_; lean_object* v_res_1342_; 
v_sz_boxed_1340_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(v_sz_boxed_1340_, v_i_boxed_1341_, v_bs_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b1_1343_, lean_object* v_constName_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_1344_, v___y_1345_, v___y_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b1_1349_, v_constName_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1355_, lean_object* v_ref_1356_, lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_1356_, v_constName_1357_, v___y_1358_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_ref_1363_, lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b1_1362_, v_ref_1363_, v_constName_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_ref_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b1_1369_, lean_object* v_ref_1370_, lean_object* v_msg_1371_, lean_object* v_declHint_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_1370_, v_msg_1371_, v_declHint_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_ref_1378_, lean_object* v_msg_1379_, lean_object* v_declHint_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(v_00_u03b1_1377_, v_ref_1378_, v_msg_1379_, v_declHint_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1378_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(lean_object* v_msg_1385_, lean_object* v_declHint_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1385_, v_declHint_1386_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1391_, lean_object* v_declHint_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(v_msg_1391_, v_declHint_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(lean_object* v_00_u03b1_1397_, lean_object* v_ref_1398_, lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1398_, v_msg_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_ref_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(v_00_u03b1_1404_, v_ref_1405_, v_msg_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v_ref_1405_);
return v_res_1410_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_linter_deprecated_arg = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_linter_deprecated_arg);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedArgExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedArgExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedArg(builtin);
}
#ifdef __cplusplus
}
#endif

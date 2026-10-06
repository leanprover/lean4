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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 138, .m_capacity = 138, .m_length = 137, .m_data = "`[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is still a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`; rename it to `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` is not a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`; remove it before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Invalid `[deprecated_arg]` attribute syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 7, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 182, 86, 230, 168, 246, 164, 173)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark a parameter as deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_109_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_107_, v___x_111_, v___x_112_, v_b_100_);
v___y_102_ = v___x_113_;
goto v___jp_101_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_114_, v_i_boxed_118_, v_stop_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object* v_initState_121_, lean_object* v_as_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_get_size(v_as_122_);
v___x_125_ = lean_nat_dec_lt(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v_initState_121_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_124_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_122_, v___x_126_, v___x_127_, v_initState_121_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_129_, lean_object* v_as_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_129_, v_as_130_);
lean_dec_ref(v_as_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_));
v___x_151_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object* v_env_154_, lean_object* v_declName_155_, lean_object* v_argName_156_){
_start:
{
lean_object* v___x_157_; lean_object* v_toEnvExtension_158_; lean_object* v_asyncMode_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_158_ = lean_ctor_get(v___x_157_, 0);
v_asyncMode_159_ = lean_ctor_get(v_toEnvExtension_158_, 2);
v___x_160_ = lean_box(1);
v___x_161_ = lean_box(0);
v___x_162_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_160_, v___x_157_, v_env_154_, v_asyncMode_159_, v___x_161_);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_162_, v_declName_155_);
lean_dec(v___x_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___x_166_; 
v_val_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_163_, 1);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_165_, v_argName_156_);
lean_dec(v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object* v_env_167_, lean_object* v_declName_168_, lean_object* v_argName_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_167_, v_declName_168_, v_argName_169_);
lean_dec(v_argName_169_);
lean_dec(v_declName_168_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__0));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__2));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__4));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__6));
v___x_182_ = l_Lean_stringToMessageData(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__8));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__10));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object* v_entry_189_){
_start:
{
lean_object* v_declName_190_; lean_object* v_oldArg_191_; lean_object* v_newArg_x3f_192_; lean_object* v_text_x3f_193_; lean_object* v___y_195_; 
v_declName_190_ = lean_ctor_get(v_entry_189_, 0);
lean_inc(v_declName_190_);
v_oldArg_191_ = lean_ctor_get(v_entry_189_, 1);
lean_inc(v_oldArg_191_);
v_newArg_x3f_192_ = lean_ctor_get(v_entry_189_, 2);
lean_inc(v_newArg_x3f_192_);
v_text_x3f_193_ = lean_ctor_get(v_entry_189_, 3);
lean_inc(v_text_x3f_193_);
lean_dec_ref(v_entry_189_);
if (lean_obj_tag(v_newArg_x3f_192_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_202_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = 0;
v___x_207_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_206_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__7, &l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___y_195_ = v___x_210_;
goto v___jp_194_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_val_211_ = lean_ctor_get(v_newArg_x3f_192_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v_newArg_x3f_192_, 1);
v___x_212_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_213_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = 0;
v___x_218_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_217_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_216_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__9, &l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofName(v_val_211_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__11, &l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___y_195_ = v___x_225_;
goto v___jp_194_;
}
v___jp_194_:
{
if (lean_obj_tag(v_text_x3f_193_) == 0)
{
return v___y_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_val_196_ = lean_ctor_get(v_text_x3f_193_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_text_x3f_193_, 1);
v___x_197_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__1, &l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1);
v___x_198_ = l_Lean_stringToMessageData(v_val_196_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(lean_object* v_k_226_, lean_object* v_b_227_, lean_object* v_c_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
v___x_234_ = lean_apply_7(v_k_226_, v_b_227_, v_c_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed(lean_object* v_k_235_, lean_object* v_b_236_, lean_object* v_c_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0(v_k_235_, v_b_236_, v_c_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(lean_object* v_type_244_, lean_object* v_k_245_, uint8_t v_cleanupAnnotations_246_, uint8_t v_whnfType_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_253_, 0, v_k_245_);
v___x_254_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_244_, v___f_253_, v_cleanupAnnotations_246_, v_whnfType_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_254_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_type_271_, lean_object* v_k_272_, lean_object* v_cleanupAnnotations_273_, lean_object* v_whnfType_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_280_; uint8_t v_whnfType_boxed_281_; lean_object* v_res_282_; 
v_cleanupAnnotations_boxed_280_ = lean_unbox(v_cleanupAnnotations_273_);
v_whnfType_boxed_281_ = lean_unbox(v_whnfType_274_);
v_res_282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_271_, v_k_272_, v_cleanupAnnotations_boxed_280_, v_whnfType_boxed_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_283_, lean_object* v_type_284_, lean_object* v_k_285_, uint8_t v_cleanupAnnotations_286_, uint8_t v_whnfType_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v_type_284_, v_k_285_, v_cleanupAnnotations_286_, v_whnfType_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_294_, lean_object* v_type_295_, lean_object* v_k_296_, lean_object* v_cleanupAnnotations_297_, lean_object* v_whnfType_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_304_; uint8_t v_whnfType_boxed_305_; lean_object* v_res_306_; 
v_cleanupAnnotations_boxed_304_ = lean_unbox(v_cleanupAnnotations_297_);
v_whnfType_boxed_305_ = lean_unbox(v_whnfType_298_);
v_res_306_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5(v_00_u03b1_294_, v_type_295_, v_k_296_, v_cleanupAnnotations_boxed_304_, v_whnfType_boxed_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_bs_309_);
return v___x_315_;
}
else
{
lean_object* v_v_316_; lean_object* v___x_317_; lean_object* v_bs_x27_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_v_316_ = lean_array_uget(v_bs_309_, v_i_308_);
v___x_317_ = lean_unsigned_to_nat(0u);
v_bs_x27_318_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_317_);
v___x_319_ = l_Lean_Expr_fvarId_x21(v_v_316_);
lean_dec(v_v_316_);
v___x_320_ = l_Lean_FVarId_getDecl___redArg(v___x_319_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = l_Lean_LocalDecl_userName(v_a_321_);
lean_dec(v_a_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_308_, v___x_323_);
v___x_325_ = lean_array_uset(v_bs_x27_318_, v_i_308_, v___x_322_);
v_i_308_ = v___x_324_;
v_bs_309_ = v___x_325_;
goto _start;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_x27_318_);
v_a_327_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_320_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_343_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_sz_boxed_342_, v_i_boxed_343_, v_bs_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v_xs_345_, lean_object* v_x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_352_; size_t v___x_353_; lean_object* v___x_354_; 
v_sz_352_ = lean_array_size(v_xs_345_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_sz_352_, v___x_353_, v_xs_345_, v___y_347_, v___y_349_, v___y_350_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v_xs_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v_xs_355_, v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_x_356_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_addEntryFn_366_; lean_object* v_importedEntries_367_; lean_object* v_state_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_addEntryFn_366_ = lean_ctor_get(v___x_363_, 3);
lean_inc(v_addEntryFn_366_);
lean_dec_ref(v___x_363_);
v_importedEntries_367_ = lean_ctor_get(v_s_365_, 0);
v_state_368_ = lean_ctor_get(v_s_365_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_s_365_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v_s_365_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_state_368_);
lean_inc(v_importedEntries_367_);
lean_dec(v_s_365_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v_state_372_; lean_object* v___x_374_; 
v_state_372_ = lean_apply_2(v_addEntryFn_366_, v_state_368_, v___x_364_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_state_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_importedEntries_367_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_state_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(lean_object* v_oldArg_377_, lean_object* v_as_378_, size_t v_i_379_, size_t v_stop_380_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_eq(v_i_379_, v_stop_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_uget_borrowed(v_as_378_, v_i_379_);
v___x_383_ = lean_name_eq(v___x_382_, v_oldArg_377_);
if (v___x_383_ == 0)
{
size_t v___x_384_; size_t v___x_385_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_379_, v___x_384_);
v_i_379_ = v___x_385_;
goto _start;
}
else
{
return v___x_383_;
}
}
else
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3___boxed(lean_object* v_oldArg_388_, lean_object* v_as_389_, lean_object* v_i_390_, lean_object* v_stop_391_){
_start:
{
size_t v_i_boxed_392_; size_t v_stop_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_i_boxed_392_ = lean_unbox_usize(v_i_390_);
lean_dec(v_i_390_);
v_stop_boxed_393_ = lean_unbox_usize(v_stop_391_);
lean_dec(v_stop_391_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_oldArg_388_, v_as_389_, v_i_boxed_392_, v_stop_boxed_393_);
lean_dec_ref(v_as_389_);
lean_dec(v_oldArg_388_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_396_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
lean_ctor_set(v___x_402_, 3, v___x_401_);
lean_ctor_set(v___x_402_, 4, v___x_400_);
lean_ctor_set(v___x_402_, 5, v___x_400_);
lean_ctor_set(v___x_402_, 6, v___x_400_);
lean_ctor_set(v___x_402_, 7, v___x_400_);
lean_ctor_set(v___x_402_, 8, v___x_400_);
lean_ctor_set(v___x_402_, 9, v___x_400_);
lean_ctor_set(v___x_402_, 10, v___x_400_);
lean_ctor_set(v___x_402_, 11, v___x_399_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(32u);
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_406_ = ((size_t)5ULL);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_unsigned_to_nat(32u);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
v___x_410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_411_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
lean_ctor_set(v___x_411_, 2, v___x_407_);
lean_ctor_set(v___x_411_, 3, v___x_407_);
lean_ctor_set_usize(v___x_411_, 4, v___x_406_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_box(1);
v___x_413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_toCold_421_; lean_object* v_env_422_; lean_object* v_options_423_; uint8_t v___x_424_; lean_object* v_env_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_420_ = lean_st_ref_get(v___y_418_);
v_toCold_421_ = lean_ctor_get(v___y_417_, 0);
v_env_422_ = lean_ctor_get(v___x_420_, 0);
lean_inc_ref(v_env_422_);
lean_dec(v___x_420_);
v_options_423_ = lean_ctor_get(v_toCold_421_, 2);
v___x_424_ = 0;
v_env_425_ = l_Lean_Environment_setRecordingDeps(v_env_422_, v___x_424_);
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_427_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_423_);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v_env_425_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
lean_ctor_set(v___x_428_, 3, v_options_423_);
v___x_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_msgData_416_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1(v_msgData_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(lean_object* v_opts_436_, lean_object* v_opt_437_){
_start:
{
lean_object* v_name_438_; lean_object* v_defValue_439_; lean_object* v_map_440_; lean_object* v___x_441_; 
v_name_438_ = lean_ctor_get(v_opt_437_, 0);
v_defValue_439_ = lean_ctor_get(v_opt_437_, 1);
v_map_440_ = lean_ctor_get(v_opts_436_, 0);
v___x_441_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_440_, v_name_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = lean_unbox(v_defValue_439_);
return v___x_442_;
}
else
{
lean_object* v_val_443_; 
v_val_443_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_441_, 1);
if (lean_obj_tag(v_val_443_) == 1)
{
uint8_t v_v_444_; 
v_v_444_ = lean_ctor_get_uint8(v_val_443_, 0);
lean_dec_ref_known(v_val_443_, 0);
return v_v_444_;
}
else
{
uint8_t v___x_445_; 
lean_dec(v_val_443_);
v___x_445_ = lean_unbox(v_defValue_439_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_opts_446_, lean_object* v_opt_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(v_opts_446_, v_opt_447_);
lean_dec_ref(v_opt_447_);
lean_dec_ref(v_opts_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_457_, uint8_t v___y_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 1)
{
lean_object* v_pre_460_; 
v_pre_460_ = lean_ctor_get(v_x_459_, 0);
switch(lean_obj_tag(v_pre_460_))
{
case 1:
{
lean_object* v_pre_461_; 
v_pre_461_ = lean_ctor_get(v_pre_460_, 0);
switch(lean_obj_tag(v_pre_461_))
{
case 0:
{
lean_object* v_str_462_; lean_object* v_str_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_str_462_ = lean_ctor_get(v_x_459_, 1);
v_str_463_ = lean_ctor_get(v_pre_460_, 1);
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_465_ = lean_string_dec_eq(v_str_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0));
v___x_467_ = lean_string_dec_eq(v_str_463_, v___x_466_);
if (v___x_467_ == 0)
{
return v___x_467_;
}
else
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1));
v___x_469_ = lean_string_dec_eq(v_str_462_, v___x_468_);
if (v___x_469_ == 0)
{
return v___x_469_;
}
else
{
return v_suppressElabErrors_457_;
}
}
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2));
v___x_471_ = lean_string_dec_eq(v_str_462_, v___x_470_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
return v_suppressElabErrors_457_;
}
}
}
case 1:
{
lean_object* v_pre_472_; 
v_pre_472_ = lean_ctor_get(v_pre_461_, 0);
if (lean_obj_tag(v_pre_472_) == 0)
{
lean_object* v_str_473_; lean_object* v_str_474_; lean_object* v_str_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_str_473_ = lean_ctor_get(v_x_459_, 1);
v_str_474_ = lean_ctor_get(v_pre_460_, 1);
v_str_475_ = lean_ctor_get(v_pre_461_, 1);
v___x_476_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3));
v___x_477_ = lean_string_dec_eq(v_str_475_, v___x_476_);
if (v___x_477_ == 0)
{
return v___x_477_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4));
v___x_479_ = lean_string_dec_eq(v_str_474_, v___x_478_);
if (v___x_479_ == 0)
{
return v___x_479_;
}
else
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5));
v___x_481_ = lean_string_dec_eq(v_str_473_, v___x_480_);
if (v___x_481_ == 0)
{
return v___x_481_;
}
else
{
return v_suppressElabErrors_457_;
}
}
}
}
else
{
return v___y_458_;
}
}
default: 
{
return v___y_458_;
}
}
}
case 0:
{
lean_object* v_str_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_str_482_ = lean_ctor_get(v_x_459_, 1);
v___x_483_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6));
v___x_484_ = lean_string_dec_eq(v_str_482_, v___x_483_);
if (v___x_484_ == 0)
{
return v___x_484_;
}
else
{
return v_suppressElabErrors_457_;
}
}
default: 
{
return v___y_458_;
}
}
}
else
{
return v___y_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_485_, lean_object* v___y_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_suppressElabErrors_boxed_488_; uint8_t v___y_8953__boxed_489_; uint8_t v_res_490_; lean_object* v_r_491_; 
v_suppressElabErrors_boxed_488_ = lean_unbox(v_suppressElabErrors_485_);
v___y_8953__boxed_489_ = lean_unbox(v___y_486_);
v_res_490_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_488_, v___y_8953__boxed_489_, v_x_487_);
lean_dec(v_x_487_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_ref_493_, lean_object* v_msgData_494_, uint8_t v_severity_495_, uint8_t v_isSilent_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v_toCold_508_; lean_object* v___y_509_; lean_object* v___y_538_; lean_object* v___y_539_; uint8_t v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; uint8_t v___y_568_; uint8_t v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; uint8_t v___y_575_; uint8_t v___y_576_; uint8_t v___y_577_; uint8_t v___x_588_; uint8_t v___y_590_; uint8_t v___y_591_; uint8_t v___y_592_; uint8_t v___y_594_; uint8_t v___x_602_; 
v___x_588_ = 2;
v___x_602_ = l_Lean_instBEqMessageSeverity_beq(v_severity_495_, v___x_588_);
if (v___x_602_ == 0)
{
v___y_594_ = v___x_602_;
goto v___jp_593_;
}
else
{
uint8_t v___x_603_; 
lean_inc_ref(v_msgData_494_);
v___x_603_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_494_);
v___y_594_ = v___x_603_;
goto v___jp_593_;
}
v___jp_500_:
{
lean_object* v_currNamespace_510_; lean_object* v_openDecls_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v_nextMacroScope_517_; lean_object* v_ngen_518_; lean_object* v_auxDeclNGen_519_; lean_object* v_traceState_520_; lean_object* v_cache_521_; lean_object* v_recordedDeps_522_; lean_object* v_messages_523_; lean_object* v_infoState_524_; lean_object* v_snapshotTasks_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_536_; 
v_currNamespace_510_ = lean_ctor_get(v_toCold_508_, 4);
v_openDecls_511_ = lean_ctor_get(v_toCold_508_, 5);
lean_inc(v_openDecls_511_);
lean_inc(v_currNamespace_510_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_currNamespace_510_);
lean_ctor_set(v___x_512_, 1, v_openDecls_511_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___y_506_);
lean_inc_ref(v___y_503_);
lean_inc_ref(v___y_505_);
v___x_514_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_514_, 0, v___y_505_);
lean_ctor_set(v___x_514_, 1, v___y_507_);
lean_ctor_set(v___x_514_, 2, v___y_504_);
lean_ctor_set(v___x_514_, 3, v___y_503_);
lean_ctor_set(v___x_514_, 4, v___x_513_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5, v___y_502_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5 + 1, v___y_501_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5 + 2, v_isSilent_496_);
v___x_515_ = lean_st_ref_take(v___y_509_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
v_nextMacroScope_517_ = lean_ctor_get(v___x_515_, 1);
v_ngen_518_ = lean_ctor_get(v___x_515_, 2);
v_auxDeclNGen_519_ = lean_ctor_get(v___x_515_, 3);
v_traceState_520_ = lean_ctor_get(v___x_515_, 4);
v_cache_521_ = lean_ctor_get(v___x_515_, 5);
v_recordedDeps_522_ = lean_ctor_get(v___x_515_, 6);
v_messages_523_ = lean_ctor_get(v___x_515_, 7);
v_infoState_524_ = lean_ctor_get(v___x_515_, 8);
v_snapshotTasks_525_ = lean_ctor_get(v___x_515_, 9);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_536_ == 0)
{
v___x_527_ = v___x_515_;
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snapshotTasks_525_);
lean_inc(v_infoState_524_);
lean_inc(v_messages_523_);
lean_inc(v_recordedDeps_522_);
lean_inc(v_cache_521_);
lean_inc(v_traceState_520_);
lean_inc(v_auxDeclNGen_519_);
lean_inc(v_ngen_518_);
lean_inc(v_nextMacroScope_517_);
lean_inc(v_env_516_);
lean_dec(v___x_515_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_MessageLog_add(v___x_514_, v_messages_523_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 7, v___x_530_);
v___x_532_ = v___x_527_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_env_516_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_nextMacroScope_517_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_ngen_518_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_auxDeclNGen_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_traceState_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 5, v_cache_521_);
lean_ctor_set(v_reuseFailAlloc_535_, 6, v_recordedDeps_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 7, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_535_, 8, v_infoState_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 9, v_snapshotTasks_525_);
v___x_532_ = v_reuseFailAlloc_535_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_st_ref_put(v___y_509_, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_529_);
return v___x_534_;
}
}
}
v___jp_537_:
{
lean_object* v_fileName_546_; lean_object* v_fileMap_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_fileName_546_ = lean_ctor_get(v___y_543_, 0);
v_fileMap_547_ = lean_ctor_get(v___y_543_, 1);
v___x_548_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_494_);
v___x_549_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1(v___x_548_, v___y_497_, v___y_498_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_563_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_inc_ref_n(v_fileMap_547_, 2);
v___x_554_ = l_Lean_FileMap_toPosition(v_fileMap_547_, v___y_541_);
lean_dec(v___y_541_);
v___x_555_ = l_Lean_FileMap_toPosition(v_fileMap_547_, v___y_545_);
lean_dec(v___y_545_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0));
if (v___y_544_ == 0)
{
lean_del_object(v___x_552_);
lean_dec_ref(v___y_538_);
v___y_501_ = v___y_540_;
v___y_502_ = v___y_542_;
v___y_503_ = v___x_557_;
v___y_504_ = v___x_556_;
v___y_505_ = v_fileName_546_;
v___y_506_ = v_a_550_;
v___y_507_ = v___x_554_;
v_toCold_508_ = v___y_539_;
v___y_509_ = v___y_498_;
goto v___jp_500_;
}
else
{
uint8_t v___x_558_; 
lean_inc(v_a_550_);
v___x_558_ = l_Lean_MessageData_hasTag(v___y_538_, v_a_550_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec_ref_known(v___x_556_, 1);
lean_dec_ref(v___x_554_);
lean_dec(v_a_550_);
v___x_559_ = lean_box(0);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_559_);
v___x_561_ = v___x_552_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_del_object(v___x_552_);
v___y_501_ = v___y_540_;
v___y_502_ = v___y_542_;
v___y_503_ = v___x_557_;
v___y_504_ = v___x_556_;
v___y_505_ = v_fileName_546_;
v___y_506_ = v_a_550_;
v___y_507_ = v___x_554_;
v_toCold_508_ = v___y_539_;
v___y_509_ = v___y_498_;
goto v___jp_500_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Syntax_getTailPos_x3f(v___y_570_, v___y_569_);
lean_dec(v___y_570_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_inc(v___y_571_);
v___y_538_ = v___y_565_;
v___y_539_ = v___y_566_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_571_;
v___y_542_ = v___y_569_;
v___y_543_ = v___y_566_;
v___y_544_ = v___y_567_;
v___y_545_ = v___y_571_;
goto v___jp_537_;
}
else
{
lean_object* v_val_573_; 
v_val_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___x_572_, 1);
v___y_538_ = v___y_565_;
v___y_539_ = v___y_566_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_571_;
v___y_542_ = v___y_569_;
v___y_543_ = v___y_566_;
v___y_544_ = v___y_567_;
v___y_545_ = v_val_573_;
goto v___jp_537_;
}
}
v___jp_574_:
{
lean_object* v_toCold_578_; lean_object* v_ref_579_; uint8_t v_suppressElabErrors_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v_ref_584_; lean_object* v___x_585_; 
v_toCold_578_ = lean_ctor_get(v___y_497_, 0);
v_ref_579_ = lean_ctor_get(v___y_497_, 2);
v_suppressElabErrors_580_ = lean_ctor_get_uint8(v___y_497_, sizeof(void*)*3 + 2);
v___x_581_ = lean_box(v_suppressElabErrors_580_);
v___x_582_ = lean_box(v___y_575_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_583_, 0, v___x_581_);
lean_closure_set(v___f_583_, 1, v___x_582_);
v_ref_584_ = l_Lean_replaceRef(v_ref_493_, v_ref_579_);
v___x_585_ = l_Lean_Syntax_getPos_x3f(v_ref_584_, v___y_576_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___y_565_ = v___f_583_;
v___y_566_ = v_toCold_578_;
v___y_567_ = v_suppressElabErrors_580_;
v___y_568_ = v___y_577_;
v___y_569_ = v___y_576_;
v___y_570_ = v_ref_584_;
v___y_571_ = v___x_586_;
goto v___jp_564_;
}
else
{
lean_object* v_val_587_; 
v_val_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_585_, 1);
v___y_565_ = v___f_583_;
v___y_566_ = v_toCold_578_;
v___y_567_ = v_suppressElabErrors_580_;
v___y_568_ = v___y_577_;
v___y_569_ = v___y_576_;
v___y_570_ = v_ref_584_;
v___y_571_ = v_val_587_;
goto v___jp_564_;
}
}
v___jp_589_:
{
if (v___y_592_ == 0)
{
v___y_575_ = v___y_590_;
v___y_576_ = v___y_591_;
v___y_577_ = v_severity_495_;
goto v___jp_574_;
}
else
{
v___y_575_ = v___y_590_;
v___y_576_ = v___y_591_;
v___y_577_ = v___x_588_;
goto v___jp_574_;
}
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 1;
v___x_596_ = l_Lean_instBEqMessageSeverity_beq(v_severity_495_, v___x_595_);
if (v___x_596_ == 0)
{
v___y_590_ = v___y_594_;
v___y_591_ = v___y_594_;
v___y_592_ = v___x_596_;
goto v___jp_589_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_497_);
v___x_598_ = l_Lean_warningAsError;
v___x_599_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(v___x_597_, v___x_598_);
lean_dec_ref(v___x_597_);
v___y_590_ = v___y_594_;
v___y_591_ = v___y_594_;
v___y_592_ = v___x_599_;
goto v___jp_589_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref(v_msgData_494_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object* v_ref_604_, lean_object* v_msgData_605_, lean_object* v_severity_606_, lean_object* v_isSilent_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_severity_boxed_611_; uint8_t v_isSilent_boxed_612_; lean_object* v_res_613_; 
v_severity_boxed_611_ = lean_unbox(v_severity_606_);
v_isSilent_boxed_612_ = lean_unbox(v_isSilent_607_);
v_res_613_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_604_, v_msgData_605_, v_severity_boxed_611_, v_isSilent_boxed_612_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v_ref_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_msgData_614_, uint8_t v_severity_615_, uint8_t v_isSilent_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_ref_620_; lean_object* v___x_621_; 
v_ref_620_ = lean_ctor_get(v___y_617_, 2);
v___x_621_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_620_, v_msgData_614_, v_severity_615_, v_isSilent_616_, v___y_617_, v___y_618_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_msgData_622_, lean_object* v_severity_623_, lean_object* v_isSilent_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v_severity_boxed_628_; uint8_t v_isSilent_boxed_629_; lean_object* v_res_630_; 
v_severity_boxed_628_ = lean_unbox(v_severity_623_);
v_isSilent_boxed_629_ = lean_unbox(v_isSilent_624_);
v_res_630_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3(v_msgData_622_, v_severity_boxed_628_, v_isSilent_boxed_629_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v___x_635_ = 1;
v___x_636_ = 0;
v___x_637_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2_spec__3(v_msgData_631_, v___x_635_, v___x_636_, v___y_632_, v___y_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2___boxed(lean_object* v_msgData_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v_msgData_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_ref_647_; lean_object* v___x_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_ref_647_ = lean_ctor_get(v___y_644_, 2);
v___x_648_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1(v_msg_643_, v___y_644_, v___y_645_);
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
lean_inc(v_ref_647_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v_ref_647_);
lean_ctor_set(v___x_653_, 1, v_a_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v_msg_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_663_, lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_toCold_668_; lean_object* v_currRecDepth_669_; lean_object* v_ref_670_; uint16_t v_optionFlags_671_; uint8_t v_suppressElabErrors_672_; uint8_t v_isRecordingDeps_673_; lean_object* v_ref_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_toCold_668_ = lean_ctor_get(v___y_665_, 0);
v_currRecDepth_669_ = lean_ctor_get(v___y_665_, 1);
v_ref_670_ = lean_ctor_get(v___y_665_, 2);
v_optionFlags_671_ = lean_ctor_get_uint16(v___y_665_, sizeof(void*)*3);
v_suppressElabErrors_672_ = lean_ctor_get_uint8(v___y_665_, sizeof(void*)*3 + 2);
v_isRecordingDeps_673_ = lean_ctor_get_uint8(v___y_665_, sizeof(void*)*3 + 3);
v_ref_674_ = l_Lean_replaceRef(v_ref_663_, v_ref_670_);
lean_inc(v_currRecDepth_669_);
lean_inc_ref(v_toCold_668_);
v___x_675_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_675_, 0, v_toCold_668_);
lean_ctor_set(v___x_675_, 1, v_currRecDepth_669_);
lean_ctor_set(v___x_675_, 2, v_ref_674_);
lean_ctor_set_uint16(v___x_675_, sizeof(void*)*3, v_optionFlags_671_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*3 + 2, v_suppressElabErrors_672_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*3 + 3, v_isRecordingDeps_673_);
v___x_676_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v_msg_664_, v___x_675_, v___y_666_);
lean_dec_ref_known(v___x_675_, 3);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_677_, lean_object* v_msg_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg(v_ref_677_, v_msg_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v_ref_677_);
return v_res_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__0));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__2));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_704_, lean_object* v_declHint_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_env_710_; uint8_t v___x_711_; 
v___x_708_ = lean_box(0);
v___x_709_ = lean_st_ref_get(v___y_706_);
v_env_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_709_);
v___x_711_ = l_Lean_Name_isAnonymous(v_declHint_705_);
if (v___x_711_ == 0)
{
uint8_t v_isExporting_712_; 
v_isExporting_712_ = lean_ctor_get_uint8(v_env_710_, sizeof(void*)*13);
if (v_isExporting_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_msg_704_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
lean_inc_ref(v_env_710_);
v___x_714_ = l_Lean_Environment_setExporting(v_env_710_, v___x_711_);
lean_inc(v_declHint_705_);
lean_inc_ref(v___x_714_);
v___x_715_ = l_Lean_Environment_contains(v___x_714_, v_declHint_705_, v_isExporting_712_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msg_704_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_c_722_; lean_object* v___x_723_; 
v___x_717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_718_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__5);
v___x_719_ = l_Lean_Options_empty;
v___x_720_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_720_, 0, v___x_714_);
lean_ctor_set(v___x_720_, 1, v___x_717_);
lean_ctor_set(v___x_720_, 2, v___x_718_);
lean_ctor_set(v___x_720_, 3, v___x_719_);
lean_inc(v_declHint_705_);
v___x_721_ = l_Lean_MessageData_ofConstName(v_declHint_705_, v___x_711_);
v_c_722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_722_, 0, v___x_720_);
lean_ctor_set(v_c_722_, 1, v___x_721_);
v___x_723_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_710_, v_declHint_705_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_c_722_);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_MessageData_note(v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v_msg_704_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_765_; 
v_val_731_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_765_ == 0)
{
v___x_733_ = v___x_723_;
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_723_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_mod_737_; uint8_t v___x_738_; 
v___x_735_ = l_Lean_Environment_header(v_env_710_);
lean_dec_ref(v_env_710_);
v___x_736_ = l_Lean_EnvironmentHeader_moduleNames(v___x_735_);
v_mod_737_ = lean_array_get(v___x_708_, v___x_736_, v_val_731_);
lean_dec(v_val_731_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_isPrivateName(v_declHint_705_);
lean_dec(v_declHint_705_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_c_722_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_ofName(v_mod_737_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_MessageData_note(v___x_746_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v_msg_704_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_748_);
v___x_750_ = v___x_733_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_c_722_);
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_MessageData_ofName(v_mod_737_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_MessageData_note(v___x_759_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v_msg_704_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_761_);
v___x_763_ = v___x_733_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_766_; 
lean_dec_ref(v_env_710_);
lean_dec(v_declHint_705_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_msg_704_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_767_, lean_object* v_declHint_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_767_, v_declHint_768_, v___y_769_);
lean_dec(v___y_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12(lean_object* v_msg_772_, lean_object* v_declHint_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v___x_777_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_772_, v_declHint_773_, v___y_775_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = l_Lean_unknownIdentifierMessageTag;
v___x_783_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_788_, lean_object* v_declHint_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12(v_msg_788_, v_declHint_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_ref_794_, lean_object* v_msg_795_, lean_object* v_declHint_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_a_801_; lean_object* v___x_802_; 
v___x_800_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12(v_msg_795_, v_declHint_796_, v___y_797_, v___y_798_);
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg(v_ref_794_, v_a_801_, v___y_797_, v___y_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v_declHint_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg(v_ref_803_, v_msg_804_, v_declHint_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v_ref_803_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__0));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__2));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(lean_object* v_ref_816_, lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__1);
v___x_822_ = 0;
lean_inc(v_constName_817_);
v___x_823_ = l_Lean_MessageData_ofConstName(v_constName_817_, v___x_822_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_821_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg(v_ref_816_, v___x_826_, v_constName_817_, v___y_818_, v___y_819_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_ref_828_, lean_object* v_constName_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_ref_828_, v_constName_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v_ref_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_constName_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_ref_838_; lean_object* v___x_839_; 
v_ref_838_ = lean_ctor_get(v___y_835_, 2);
v___x_839_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_ref_838_, v_constName_834_, v___y_835_, v___y_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_constName_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg(v_constName_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(lean_object* v_constName_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_env_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_849_ = lean_st_ref_get(v___y_847_);
v_env_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_env_850_);
lean_dec(v___x_849_);
v___x_851_ = 0;
lean_inc(v_constName_845_);
v___x_852_ = l_Lean_Environment_find_x3f(v_env_850_, v_constName_845_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg(v_constName_845_, v___y_846_, v___y_847_);
return v___x_853_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_constName_845_);
v_val_854_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 0);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_val_854_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4___boxed(lean_object* v_constName_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(v_constName_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_866_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_875_ = l_Lean_MessageData_ofFormat(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_894_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
lean_ctor_set(v___x_894_, 3, v___x_893_);
lean_ctor_set(v___x_894_, 4, v___x_893_);
lean_ctor_set(v___x_894_, 5, v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
lean_ctor_set(v___x_896_, 3, v___x_895_);
lean_ctor_set(v___x_896_, 4, v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___f_905_, lean_object* v___x_906_, lean_object* v_declName_907_, lean_object* v_stx_908_, uint8_t v___kind_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_nextMacroScope_914_; lean_object* v_ngen_915_; lean_object* v_auxDeclNGen_916_; lean_object* v_traceState_917_; lean_object* v_recordedDeps_918_; lean_object* v_messages_919_; lean_object* v_infoState_920_; lean_object* v_snapshotTasks_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v_a_1019_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; 
v___x_929_ = l_Lean_Name_mkStr2(v___x_900_, v___x_901_);
lean_inc(v_stx_908_);
v___x_930_ = l_Lean_Syntax_isOfKind(v_stx_908_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___x_1138_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1139_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1138_, v___y_910_, v___y_911_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v_oldId_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_since_x3f_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v_text_x3f_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_newId_x3f_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1140_ = lean_unsigned_to_nat(1u);
v_oldId_1141_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1140_);
v___x_1188_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_906_);
v___x_1189_ = l_Lean_Syntax_isNone(v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
lean_inc(v___x_1188_);
v___x_1190_ = l_Lean_Syntax_matchesNull(v___x_1188_, v___x_1140_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v___x_1188_);
lean_dec(v_oldId_1141_);
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___x_1191_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1192_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1191_, v___y_910_, v___y_911_);
return v___x_1192_;
}
else
{
lean_object* v_newId_x3f_1193_; lean_object* v___x_1194_; 
v_newId_x3f_1193_ = l_Lean_Syntax_getArg(v___x_1188_, v___x_903_);
lean_dec(v___x_1188_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_newId_x3f_1193_);
v_newId_x3f_1176_ = v___x_1194_;
v___y_1177_ = v___y_910_;
v___y_1178_ = v___y_911_;
goto v___jp_1175_;
}
}
else
{
lean_object* v___x_1195_; 
lean_dec(v___x_1188_);
v___x_1195_ = lean_box(0);
v_newId_x3f_1176_ = v___x_1195_;
v___y_1177_ = v___y_910_;
v___y_1178_ = v___y_911_;
goto v___jp_1175_;
}
v___jp_1142_:
{
lean_object* v_oldArg_1148_; 
v_oldArg_1148_ = l_Lean_TSyntax_getId(v_oldId_1141_);
lean_dec(v_oldId_1141_);
if (lean_obj_tag(v___y_1143_) == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_box(0);
v___y_1120_ = v___y_1144_;
v___y_1121_ = v_oldArg_1148_;
v___y_1122_ = v___y_1146_;
v___y_1123_ = v_since_x3f_1145_;
v___y_1124_ = v___y_1147_;
v___y_1125_ = v___x_1149_;
goto v___jp_1119_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_val_1150_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___y_1143_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_val_1150_);
lean_dec(v___y_1143_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = l_Lean_TSyntax_getId(v_val_1150_);
lean_dec(v_val_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
v___y_1120_ = v___y_1144_;
v___y_1121_ = v_oldArg_1148_;
v___y_1122_ = v___y_1146_;
v___y_1123_ = v_since_x3f_1145_;
v___y_1124_ = v___y_1147_;
v___y_1125_ = v___x_1156_;
goto v___jp_1119_;
}
}
}
}
v___jp_1159_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(4u);
v___x_1166_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1165_);
lean_dec(v_stx_908_);
v___x_1167_ = l_Lean_Syntax_isNone(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1166_);
v___x_1169_ = l_Lean_Syntax_matchesNull(v___x_1166_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v___x_1166_);
lean_dec(v_text_x3f_1162_);
lean_dec(v___y_1160_);
lean_dec(v_oldId_1141_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___x_1170_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1171_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1170_, v___y_1163_, v___y_1164_);
return v___x_1171_;
}
else
{
lean_object* v_since_x3f_1172_; lean_object* v___x_1173_; 
v_since_x3f_1172_ = l_Lean_Syntax_getArg(v___x_1166_, v___y_1161_);
lean_dec(v___x_1166_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_since_x3f_1172_);
v___y_1143_ = v___y_1160_;
v___y_1144_ = v_text_x3f_1162_;
v_since_x3f_1145_ = v___x_1173_;
v___y_1146_ = v___y_1163_;
v___y_1147_ = v___y_1164_;
goto v___jp_1142_;
}
}
else
{
lean_object* v___x_1174_; 
lean_dec(v___x_1166_);
v___x_1174_ = lean_box(0);
v___y_1143_ = v___y_1160_;
v___y_1144_ = v_text_x3f_1162_;
v_since_x3f_1145_ = v___x_1174_;
v___y_1146_ = v___y_1163_;
v___y_1147_ = v___y_1164_;
goto v___jp_1142_;
}
}
v___jp_1175_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(3u);
v___x_1180_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_isNone(v___x_1180_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; 
lean_inc(v___x_1180_);
v___x_1182_ = l_Lean_Syntax_matchesNull(v___x_1180_, v___x_1140_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v___x_1180_);
lean_dec(v_newId_x3f_1176_);
lean_dec(v_oldId_1141_);
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___x_1183_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1184_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1183_, v___y_1177_, v___y_1178_);
return v___x_1184_;
}
else
{
lean_object* v_text_x3f_1185_; lean_object* v___x_1186_; 
v_text_x3f_1185_ = l_Lean_Syntax_getArg(v___x_1180_, v___x_903_);
lean_dec(v___x_1180_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_text_x3f_1185_);
v___y_1160_ = v_newId_x3f_1176_;
v___y_1161_ = v___x_1179_;
v_text_x3f_1162_ = v___x_1186_;
v___y_1163_ = v___y_1177_;
v___y_1164_ = v___y_1178_;
goto v___jp_1159_;
}
}
else
{
lean_object* v___x_1187_; 
lean_dec(v___x_1180_);
v___x_1187_ = lean_box(0);
v___y_1160_ = v_newId_x3f_1176_;
v___y_1161_ = v___x_1179_;
v_text_x3f_1162_ = v___x_1187_;
v___y_1163_ = v___y_1177_;
v___y_1164_ = v___y_1178_;
goto v___jp_1159_;
}
}
}
v___jp_913_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_926_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_926_, 0, v___y_924_);
lean_ctor_set(v___x_926_, 1, v_nextMacroScope_914_);
lean_ctor_set(v___x_926_, 2, v_ngen_915_);
lean_ctor_set(v___x_926_, 3, v_auxDeclNGen_916_);
lean_ctor_set(v___x_926_, 4, v_traceState_917_);
lean_ctor_set(v___x_926_, 5, v___x_925_);
lean_ctor_set(v___x_926_, 6, v_recordedDeps_918_);
lean_ctor_set(v___x_926_, 7, v_messages_919_);
lean_ctor_set(v___x_926_, 8, v_infoState_920_);
lean_ctor_set(v___x_926_, 9, v_snapshotTasks_921_);
v___x_927_ = lean_st_ref_put(v___y_922_, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___y_923_);
return v___x_928_;
}
v___jp_931_:
{
lean_object* v___x_937_; lean_object* v_env_938_; lean_object* v_nextMacroScope_939_; lean_object* v_ngen_940_; lean_object* v_auxDeclNGen_941_; lean_object* v_traceState_942_; lean_object* v_recordedDeps_943_; lean_object* v_messages_944_; lean_object* v_infoState_945_; lean_object* v_snapshotTasks_946_; lean_object* v___x_947_; lean_object* v_toEnvExtension_948_; lean_object* v_asyncMode_949_; uint8_t v_logWrites_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___f_953_; 
v___x_937_ = lean_st_ref_take(v___y_936_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_938_);
v_nextMacroScope_939_ = lean_ctor_get(v___x_937_, 1);
lean_inc(v_nextMacroScope_939_);
v_ngen_940_ = lean_ctor_get(v___x_937_, 2);
lean_inc_ref(v_ngen_940_);
v_auxDeclNGen_941_ = lean_ctor_get(v___x_937_, 3);
lean_inc_ref(v_auxDeclNGen_941_);
v_traceState_942_ = lean_ctor_get(v___x_937_, 4);
lean_inc_ref(v_traceState_942_);
v_recordedDeps_943_ = lean_ctor_get(v___x_937_, 6);
lean_inc_ref(v_recordedDeps_943_);
v_messages_944_ = lean_ctor_get(v___x_937_, 7);
lean_inc_ref(v_messages_944_);
v_infoState_945_ = lean_ctor_get(v___x_937_, 8);
lean_inc_ref(v_infoState_945_);
v_snapshotTasks_946_ = lean_ctor_get(v___x_937_, 9);
lean_inc_ref(v_snapshotTasks_946_);
lean_dec(v___x_937_);
v___x_947_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_948_ = lean_ctor_get(v___x_947_, 0);
v_asyncMode_949_ = lean_ctor_get(v_toEnvExtension_948_, 2);
v_logWrites_950_ = lean_ctor_get_uint8(v_toEnvExtension_948_, sizeof(void*)*6);
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_952_, 0, v_declName_907_);
lean_ctor_set(v___x_952_, 1, v___y_932_);
lean_ctor_set(v___x_952_, 2, v___y_934_);
lean_ctor_set(v___x_952_, 3, v___y_935_);
lean_ctor_set(v___x_952_, 4, v___y_933_);
v___f_953_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_953_, 0, v___x_947_);
lean_closure_set(v___f_953_, 1, v___x_952_);
if (v_logWrites_950_ == 0)
{
lean_object* v___x_954_; 
lean_inc_ref(v_toEnvExtension_948_);
v___x_954_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_948_, v_env_938_, v___f_953_, v_asyncMode_949_, v___x_902_, v___x_930_);
v_nextMacroScope_914_ = v_nextMacroScope_939_;
v_ngen_915_ = v_ngen_940_;
v_auxDeclNGen_916_ = v_auxDeclNGen_941_;
v_traceState_917_ = v_traceState_942_;
v_recordedDeps_918_ = v_recordedDeps_943_;
v_messages_919_ = v_messages_944_;
v_infoState_920_ = v_infoState_945_;
v_snapshotTasks_921_ = v_snapshotTasks_946_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_951_;
v___y_924_ = v___x_954_;
goto v___jp_913_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_inc_ref_n(v_toEnvExtension_948_, 2);
v___x_955_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_948_, v_env_938_);
lean_dec_ref(v_env_938_);
v___x_956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_948_, v___x_955_, v___f_953_, v_asyncMode_949_, v___x_902_, v___x_930_);
v_nextMacroScope_914_ = v_nextMacroScope_939_;
v_ngen_915_ = v_ngen_940_;
v_auxDeclNGen_916_ = v_auxDeclNGen_941_;
v_traceState_917_ = v_traceState_942_;
v_recordedDeps_918_ = v_recordedDeps_943_;
v_messages_919_ = v_messages_944_;
v_infoState_920_ = v_infoState_945_;
v_snapshotTasks_921_ = v_snapshotTasks_946_;
v___y_922_ = v___y_936_;
v___y_923_ = v___x_951_;
v___y_924_ = v___x_956_;
goto v___jp_913_;
}
}
v___jp_957_:
{
if (lean_obj_tag(v___y_959_) == 0)
{
if (v___x_930_ == 0)
{
v___y_932_ = v___y_958_;
v___y_933_ = v___y_959_;
v___y_934_ = v___y_960_;
v___y_935_ = v___y_961_;
v___y_936_ = v___y_963_;
goto v___jp_931_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_965_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__2(v___x_964_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref_known(v___x_965_, 1);
v___y_932_ = v___y_958_;
v___y_933_ = v___y_959_;
v___y_934_ = v___y_960_;
v___y_935_ = v___y_961_;
v___y_936_ = v___y_963_;
goto v___jp_931_;
}
else
{
lean_dec(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_958_);
lean_dec(v_declName_907_);
lean_dec(v___x_902_);
return v___x_965_;
}
}
}
else
{
v___y_932_ = v___y_958_;
v___y_933_ = v___y_959_;
v___y_934_ = v___y_960_;
v___y_935_ = v___y_961_;
v___y_936_ = v___y_963_;
goto v___jp_931_;
}
}
v___jp_966_:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_array_get_size(v___y_971_);
v___x_976_ = lean_nat_dec_lt(v___x_903_, v___x_975_);
lean_dec(v___x_903_);
if (v___x_976_ == 0)
{
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
v___y_958_ = v___y_967_;
v___y_959_ = v___y_968_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
goto v___jp_957_;
}
else
{
if (v___x_976_ == 0)
{
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
v___y_958_ = v___y_967_;
v___y_959_ = v___y_968_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
goto v___jp_957_;
}
else
{
size_t v___x_977_; size_t v___x_978_; uint8_t v___x_979_; 
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_975_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v___y_967_, v___y_971_, v___x_977_, v___x_978_);
lean_dec_ref(v___y_971_);
if (v___x_979_ == 0)
{
lean_dec(v___y_970_);
v___y_958_ = v___y_967_;
v___y_959_ = v___y_968_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_973_;
v___y_963_ = v___y_974_;
goto v___jp_957_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v___y_972_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
lean_dec(v___x_902_);
v___x_980_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3);
v___x_981_ = l_Lean_MessageData_ofName(v___y_967_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_MessageData_ofName(v_declName_907_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_MessageData_ofName(v___y_970_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_992_, v___y_973_, v___y_974_);
return v___x_993_;
}
}
}
}
v___jp_994_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_997_);
lean_dec(v___y_996_);
lean_dec(v___y_995_);
v___x_1003_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3);
v___x_1004_ = l_Lean_MessageData_ofName(v___y_999_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_MessageData_ofName(v_declName_907_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_1003_);
v___x_1011_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1010_, v___y_998_, v___y_1002_);
return v___x_1011_;
}
v___jp_1012_:
{
if (lean_obj_tag(v___y_1015_) == 1)
{
lean_object* v_val_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_val_1020_ = lean_ctor_get(v___y_1015_, 0);
lean_inc(v_val_1020_);
v___x_1021_ = lean_array_get_size(v_a_1019_);
v___x_1022_ = lean_nat_dec_lt(v___x_903_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1020_;
v___y_1000_ = v_a_1019_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
goto v___jp_994_;
}
else
{
if (v___x_1022_ == 0)
{
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1020_;
v___y_1000_ = v_a_1019_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
goto v___jp_994_;
}
else
{
size_t v___x_1023_; size_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_of_nat(v___x_1021_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v_val_1020_, v_a_1019_, v___x_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v_val_1020_;
v___y_1000_ = v_a_1019_;
v___y_1001_ = v___y_1017_;
v___y_1002_ = v___y_1018_;
goto v___jp_994_;
}
else
{
v___y_967_ = v___y_1013_;
v___y_968_ = v___y_1014_;
v___y_969_ = v___y_1015_;
v___y_970_ = v_val_1020_;
v___y_971_ = v_a_1019_;
v___y_972_ = v___y_1017_;
v___y_973_ = v___y_1016_;
v___y_974_ = v___y_1018_;
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_array_get_size(v_a_1019_);
v___x_1027_ = lean_nat_dec_lt(v___x_903_, v___x_1026_);
lean_dec(v___x_903_);
if (v___x_1027_ == 0)
{
lean_dec_ref(v_a_1019_);
v___y_958_ = v___y_1013_;
v___y_959_ = v___y_1014_;
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1016_;
v___y_963_ = v___y_1018_;
goto v___jp_957_;
}
else
{
if (v___x_1027_ == 0)
{
lean_dec_ref(v_a_1019_);
v___y_958_ = v___y_1013_;
v___y_959_ = v___y_1014_;
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1016_;
v___y_963_ = v___y_1018_;
goto v___jp_957_;
}
else
{
size_t v___x_1028_; size_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1026_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__3(v___y_1013_, v_a_1019_, v___x_1028_, v___x_1029_);
lean_dec_ref(v_a_1019_);
if (v___x_1030_ == 0)
{
v___y_958_ = v___y_1013_;
v___y_959_ = v___y_1014_;
v___y_960_ = v___y_1015_;
v___y_961_ = v___y_1017_;
v___y_962_ = v___y_1016_;
v___y_963_ = v___y_1018_;
goto v___jp_957_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v___y_1017_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec(v___x_902_);
v___x_1031_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___closed__3);
v___x_1032_ = l_Lean_MessageData_ofName(v___y_1013_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_MessageData_ofName(v_declName_907_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1039_, v___y_1016_, v___y_1018_);
return v___x_1040_;
}
}
}
}
}
v___jp_1041_:
{
lean_object* v___x_1048_; 
lean_inc(v_declName_907_);
v___x_1048_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4(v_declName_907_, v___y_1044_, v___y_1046_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; uint64_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_ConstantInfo_type(v_a_1049_);
lean_dec(v_a_1049_);
v___x_1051_ = 0;
v___x_1052_ = 1;
v___x_1053_ = 0;
v___x_1054_ = 2;
v___x_1055_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1055_, 0, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 1, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 2, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 3, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 4, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 5, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 6, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 7, v___x_1051_);
lean_ctor_set_uint8(v___x_1055_, 8, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 9, v___x_1052_);
lean_ctor_set_uint8(v___x_1055_, 10, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, 11, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 12, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 13, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 14, v___x_1054_);
lean_ctor_set_uint8(v___x_1055_, 15, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 16, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 17, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 18, v___x_930_);
lean_ctor_set_uint8(v___x_1055_, 19, v___x_1051_);
v___x_1056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set_uint64(v___x_1057_, sizeof(void*)*1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1059_ = lean_unsigned_to_nat(32u);
v___x_1060_ = lean_mk_empty_array_with_capacity(v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_1062_ = ((size_t)5ULL);
lean_inc_n(v___x_903_, 7);
v___x_1063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1060_);
lean_ctor_set(v___x_1063_, 2, v___x_903_);
lean_ctor_set(v___x_1063_, 3, v___x_903_);
lean_ctor_set_usize(v___x_1063_, 4, v___x_1062_);
v___x_1064_ = lean_box(1);
lean_inc_ref(v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1058_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v___x_1064_);
v___x_1066_ = lean_mk_empty_array_with_capacity(v___x_903_);
v___x_1067_ = lean_box(0);
lean_inc(v___x_904_);
v___x_1068_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1068_, 0, v___x_1057_);
lean_ctor_set(v___x_1068_, 1, v___x_904_);
lean_ctor_set(v___x_1068_, 2, v___x_1065_);
lean_ctor_set(v___x_1068_, 3, v___x_1066_);
lean_ctor_set(v___x_1068_, 4, v___x_1067_);
lean_ctor_set(v___x_1068_, 5, v___x_903_);
lean_ctor_set(v___x_1068_, 6, v___x_1067_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*7, v___x_1051_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*7 + 1, v___x_1051_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*7 + 2, v___x_1051_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*7 + 3, v___x_930_);
v___x_1069_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1070_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1070_, 0, v___x_903_);
lean_ctor_set(v___x_1070_, 1, v___x_903_);
lean_ctor_set(v___x_1070_, 2, v___x_903_);
lean_ctor_set(v___x_1070_, 3, v___x_903_);
lean_ctor_set(v___x_1070_, 4, v___x_1058_);
lean_ctor_set(v___x_1070_, 5, v___x_1058_);
lean_ctor_set(v___x_1070_, 6, v___x_1058_);
lean_ctor_set(v___x_1070_, 7, v___x_1058_);
lean_ctor_set(v___x_1070_, 8, v___x_1058_);
lean_ctor_set(v___x_1070_, 9, v___x_1058_);
lean_ctor_set(v___x_1070_, 10, v___x_1058_);
lean_ctor_set(v___x_1070_, 11, v___x_1069_);
v___x_1071_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1072_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_ctor_set(v___x_1073_, 2, v___x_904_);
lean_ctor_set(v___x_1073_, 3, v___x_1063_);
lean_ctor_set(v___x_1073_, 4, v___x_1072_);
v___x_1074_ = lean_st_mk_ref(v___x_1073_);
v___x_1075_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__5___redArg(v___x_1050_, v___f_905_, v___x_1051_, v___x_1051_, v___x_1068_, v___x_1074_, v___y_1044_, v___y_1046_);
lean_dec_ref_known(v___x_1068_, 7);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = lean_st_ref_get(v___x_1074_);
lean_dec(v___x_1074_);
lean_dec(v___x_1077_);
v___y_1013_ = v___y_1042_;
v___y_1014_ = v___y_1047_;
v___y_1015_ = v___y_1043_;
v___y_1016_ = v___y_1044_;
v___y_1017_ = v___y_1045_;
v___y_1018_ = v___y_1046_;
v_a_1019_ = v_a_1076_;
goto v___jp_1012_;
}
else
{
lean_dec(v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1078_; 
v_a_1078_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1075_, 1);
v___y_1013_ = v___y_1042_;
v___y_1014_ = v___y_1047_;
v___y_1015_ = v___y_1043_;
v___y_1016_ = v___y_1044_;
v___y_1017_ = v___y_1045_;
v___y_1018_ = v___y_1046_;
v_a_1019_ = v_a_1078_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v___y_1047_);
lean_dec(v___y_1045_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec(v_declName_907_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v_a_1079_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1075_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v___y_1047_);
lean_dec(v___y_1045_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v___x_902_);
v_a_1087_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1048_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1048_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
v___jp_1095_:
{
if (lean_obj_tag(v___y_1099_) == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_box(0);
v___y_1042_ = v___y_1096_;
v___y_1043_ = v___y_1097_;
v___y_1044_ = v___y_1098_;
v___y_1045_ = v___y_1101_;
v___y_1046_ = v___y_1100_;
v___y_1047_ = v___x_1102_;
goto v___jp_1041_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
v_val_1103_ = lean_ctor_get(v___y_1099_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_1099_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v___y_1099_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v___y_1099_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_TSyntax_getString(v_val_1103_);
lean_dec(v_val_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v___y_1042_ = v___y_1096_;
v___y_1043_ = v___y_1097_;
v___y_1044_ = v___y_1098_;
v___y_1045_ = v___y_1101_;
v___y_1046_ = v___y_1100_;
v___y_1047_ = v___x_1109_;
goto v___jp_1041_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_box(0);
v___y_1096_ = v___y_1113_;
v___y_1097_ = v___y_1114_;
v___y_1098_ = v___y_1115_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1117_;
v___y_1101_ = v___x_1118_;
goto v___jp_1095_;
}
v___jp_1119_:
{
if (lean_obj_tag(v___y_1120_) == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_box(0);
v___y_1096_ = v___y_1121_;
v___y_1097_ = v___y_1125_;
v___y_1098_ = v___y_1122_;
v___y_1099_ = v___y_1123_;
v___y_1100_ = v___y_1124_;
v___y_1101_ = v___x_1126_;
goto v___jp_1095_;
}
else
{
lean_object* v_val_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1137_; 
v_val_1127_ = lean_ctor_get(v___y_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___y_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1129_ = v___y_1120_;
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_val_1127_);
lean_dec(v___y_1120_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = l_Lean_TSyntax_getString(v_val_1127_);
lean_dec(v_val_1127_);
v___x_1132_ = lean_string_utf8_byte_size(v___x_1131_);
v___x_1133_ = lean_nat_dec_eq(v___x_1132_, v___x_903_);
if (v___x_1133_ == 0)
{
if (v___x_930_ == 0)
{
lean_dec_ref(v___x_1131_);
lean_del_object(v___x_1129_);
v___y_1113_ = v___y_1121_;
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1122_;
v___y_1116_ = v___y_1123_;
v___y_1117_ = v___y_1124_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1135_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1131_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
v___y_1096_ = v___y_1121_;
v___y_1097_ = v___y_1125_;
v___y_1098_ = v___y_1122_;
v___y_1099_ = v___y_1123_;
v___y_1100_ = v___y_1124_;
v___y_1101_ = v___x_1135_;
goto v___jp_1095_;
}
}
}
else
{
lean_dec_ref(v___x_1131_);
lean_del_object(v___x_1129_);
v___y_1113_ = v___y_1121_;
v___y_1114_ = v___y_1125_;
v___y_1115_ = v___y_1122_;
v___y_1116_ = v___y_1123_;
v___y_1117_ = v___y_1124_;
goto v___jp_1112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___f_1201_, lean_object* v___x_1202_, lean_object* v_declName_1203_, lean_object* v_stx_1204_, lean_object* v___kind_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___kind_boxed_1209_; lean_object* v_res_1210_; 
v___kind_boxed_1209_ = lean_unbox(v___kind_1205_);
v_res_1210_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_, v___f_1201_, v___x_1202_, v_declName_1203_, v_stx_1204_, v___kind_boxed_1209_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___x_1202_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1213_ = l_Lean_stringToMessageData(v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1216_ = l_Lean_stringToMessageData(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(lean_object* v___x_1217_, lean_object* v_decl_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1223_ = l_Lean_MessageData_ofName(v___x_1217_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v___x_1226_, v___y_1219_, v___y_1220_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v___x_1228_, lean_object* v_decl_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(v___x_1228_, v_decl_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v_decl_1229_);
return v_res_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_unsigned_to_nat(3249530483u);
v___x_1276_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1277_ = l_Lean_Name_num___override(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1280_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1281_ = l_Lean_Name_str___override(v___x_1280_, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1284_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1285_ = l_Lean_Name_str___override(v___x_1284_, v___x_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_unsigned_to_nat(2u);
v___x_1287_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1288_ = l_Lean_Name_num___override(v___x_1287_, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1303_ = 0;
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1305_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1306_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1307_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1304_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*3, v___x_1303_);
return v___x_1307_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___f_1308_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___f_1309_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_));
v___x_1310_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___f_1309_);
lean_ctor_set(v___x_1311_, 2, v___f_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_);
v___x_1314_ = l_Lean_registerBuiltinAttribute(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2____boxed(lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2_();
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(size_t v_sz_1317_, size_t v_i_1318_, lean_object* v_bs_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___redArg(v_sz_1317_, v_i_1318_, v_bs_1319_, v___y_1320_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0___boxed(lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_bs_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__0(v_sz_boxed_1334_, v_i_boxed_1335_, v_bs_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1337_, lean_object* v_msg_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___redArg(v_msg_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_msg_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__1(v_00_u03b1_1343_, v_msg_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b1_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___redArg(v_constName_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_constName_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b1_1355_, v_constName_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_00_u03b1_1361_, lean_object* v_ref_1362_, lean_object* v_constName_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_ref_1362_, v_constName_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_ref_1369_, lean_object* v_constName_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_00_u03b1_1368_, v_ref_1369_, v_constName_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v_ref_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1375_, lean_object* v_ref_1376_, lean_object* v_msg_1377_, lean_object* v_declHint_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___redArg(v_ref_1376_, v_msg_1377_, v_declHint_1378_, v___y_1379_, v___y_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_ref_1384_, lean_object* v_msg_1385_, lean_object* v_declHint_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11(v_00_u03b1_1383_, v_ref_1384_, v_msg_1385_, v_declHint_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_ref_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1391_, lean_object* v_declHint_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1391_, v_declHint_1392_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1397_, lean_object* v_declHint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__12_spec__13(v_msg_1397_, v_declHint_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1403_, lean_object* v_ref_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___redArg(v_ref_1404_, v_msg_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_ref_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3249530483____hygCtx___hyg_2__spec__4_spec__6_spec__9_spec__11_spec__13(v_00_u03b1_1410_, v_ref_1411_, v_msg_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v_ref_1411_);
return v_res_1416_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
